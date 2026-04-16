import { useState, useEffect, useCallback, useMemo, useSyncExternalStore } from 'react'
import { isBackendConfigured, backend } from '../backend/index.ts'
import {
  getTask, getTaskIncludingDeleted, getTasksInList, getListName, getLists, findListForTask,
  getDeletedTaskIds, getAllPriorityTasks, getAllLogbookTasks, getAllVisibleTasks,
  countPriorityTasks, countLogbookTasks,
} from '../domain.ts'
import { MultiProjectEffectManager } from './MultiProjectEffectManager.js'

export function useAllProjects(projectIds) {
  const [status, setStatus] = useState('syncing')
  const [error, setError] = useState(null)
  const [manager, setManager] = useState(null)
  const [projectMembers, setProjectMembers] = useState({})

  const projectIdsKey = projectIds?.sort().join(',') || ''

  useEffect(() => {
    if (!isBackendConfigured() || !projectIds?.length) { setManager(null); return }
    const newManager = new MultiProjectEffectManager(projectIds)
    newManager.setCallbacks(setStatus, setError)
    newManager.start()
    setManager(newManager)
    return () => { newManager.stop() }
  }, [projectIdsKey])

  // Subscribe to multi-project state
  const multiModel = useSyncExternalStore(
    manager?.subscribe ?? (() => () => {}),
    manager?.getSnapshot ?? (() => null),
    manager?.getSnapshot ?? (() => null)
  )

  // Fetch members for all projects
  useEffect(() => {
    if (!projectIds?.length || !isBackendConfigured()) return
    const fetchAllMembers = async () => {
      const membersByProject = {}
      for (const projectId of projectIds) {
        try {
          const members = await backend.members.list(projectId)
          membersByProject[projectId] = members.map(m => ({
            user_id: m.userId, role: m.role, email: m.email
          }))
        } catch (e) {
          console.error(`Error fetching members for project ${projectId}:`, e)
          membersByProject[projectId] = []
        }
      }
      setProjectMembers(membersByProject)
    }
    fetchAllMembers()
  }, [projectIds])

  const loading = status === 'syncing'

  // Build projectData from multiModel
  const projectData = useMemo(() => {
    if (!multiModel) return {}
    const data = {}
    const baseVersions = manager?.getBaseVersions() || {}
    for (const projectId of Object.keys(multiModel.projects)) {
      const model = multiModel.projects[projectId]
      if (model) data[projectId] = { model, version: baseVersions[projectId] || 0 }
    }
    return data
  }, [multiModel, manager])

  const createDispatch = useCallback((projectId) => {
    return (action) => { manager?.dispatchSingle(projectId, action) }
  }, [manager])

  const dispatch = useCallback((multiAction) => {
    manager?.dispatch(multiAction)
  }, [manager])

  const moveTaskToProject = useCallback((srcProject, dstProject, taskId, dstList, anchor = null) => {
    manager?.dispatch({ kind: 'MoveTaskTo', srcProject, dstProject, taskId, dstList, taskPlace: anchor || { kind: 'AtEnd' } })
  }, [manager])

  const copyTaskToProject = useCallback((srcProject, dstProject, taskId, dstList) => {
    manager?.dispatch({ kind: 'CopyTaskTo', srcProject, dstProject, taskId, dstList })
  }, [manager])

  const moveListToProject = useCallback((srcProject, dstProject, listId) => {
    manager?.dispatch({ kind: 'MoveListTo', srcProject, dstProject, listId })
  }, [manager])

  // Enrich a tagged task ID with full task data
  const enrichTask = useCallback((tagged) => {
    const model = projectData[tagged.projectId]?.model
    if (!model) return null
    const task = getTask(model, tagged.taskId)
    if (!task) return null
    const listId = findListForTask(model, tagged.taskId)
    return {
      id: tagged.taskId,
      projectId: tagged.projectId,
      listId,
      listName: listId !== undefined ? (getListName(model, listId) || '') : '',
      ...task
    }
  }, [projectData])

  const priorityTasks = useMemo(() => {
    if (!multiModel) return []
    return getAllPriorityTasks(multiModel).map(enrichTask).filter(t => t !== null)
  }, [multiModel, enrichTask])

  const logbookTasks = useMemo(() => {
    if (!multiModel) return []
    return getAllLogbookTasks(multiModel).map(enrichTask).filter(t => t !== null)
  }, [multiModel, enrichTask])

  const allTasks = useMemo(() => {
    if (!multiModel) return []
    return getAllVisibleTasks(multiModel).map(enrichTask).filter(t => t !== null && !t.completed)
  }, [multiModel, enrichTask])

  const trashTasks = useMemo(() => {
    if (!multiModel) return []
    const tasks = []
    for (const projectId of Object.keys(multiModel.projects)) {
      const model = multiModel.projects[projectId]
      if (!model) continue
      for (const taskId of getDeletedTaskIds(model)) {
        const task = getTaskIncludingDeleted(model, taskId)
        if (!task) continue
        const listId = task.deletedFromList
        const listName = listId !== undefined ? (getListName(model, listId) || '') : ''
        const canRestore = listId !== undefined && listName !== ''
        tasks.push({
          id: taskId, projectId, listId,
          listName: canRestore ? listName : '(list deleted)',
          canRestore, ...task
        })
      }
    }
    return tasks
  }, [multiModel])

  const getProjectModel = useCallback((projectId) => {
    return projectData[projectId]?.model || null
  }, [projectData])

  const getProjectLists = useCallback((projectId) => {
    const model = projectData[projectId]?.model
    if (!model) return []
    return getLists(model).map(id => ({ id, name: getListName(model, id) || '' }))
  }, [projectData])

  const getListTaskCount = useCallback((projectId, listId) => {
    const model = projectData[projectId]?.model
    if (!model) return 0
    return getTasksInList(model, listId).filter(id => {
      const task = getTask(model, id)
      return task && !task.completed
    }).length
  }, [projectData])

  const getProjectMembersForId = useCallback((projectId) => {
    return projectMembers[projectId] || []
  }, [projectMembers])

  const refresh = useCallback(() => manager?.sync(), [manager])
  const toggleOffline = useCallback(() => manager?.toggleOffline() ?? false, [manager])

  return {
    projectData, multiModel, loading, error, status,
    createDispatch, dispatch, moveTaskToProject, copyTaskToProject, moveListToProject,
    priorityTasks, logbookTasks, allTasks, trashTasks,
    getProjectModel, getProjectLists, getListTaskCount,
    getProjectMembers: getProjectMembersForId,
    refresh, toggleOffline,
    isOffline: manager ? !manager.isOnline : false,
    hasPending: manager?.hasPending ?? false,
    pendingCount: manager?.pendingCount ?? 0,
  }
}
