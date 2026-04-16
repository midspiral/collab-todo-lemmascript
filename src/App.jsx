import { useState, useEffect, useMemo, useCallback } from 'react'
import { Star, CheckSquare, Circle } from 'lucide-react'
import { backend, isBackendConfigured, signOut } from './backend/index.ts'
import { useProjects, useProjectMembers } from './hooks/useCollaborativeProject.js'
import { useAllProjects } from './hooks/useAllProjects.js'
import {
  getLists, getListName, getTasksInList, getTask, findListForTask,
  countPriorityTasks, countLogbookTasks,
} from './domain.ts'

import { AuthForm } from './components/auth'
import { Toast, UndoToast } from './components/common'
import { TopBar, Sidebar, MainContent, EmptyState, LoadingState, Footer } from './components/layout'
import { TaskList, TaskItem } from './components/tasks'
import { ProjectHeader, FilterTabs } from './components/project'
import { FilterBar } from './components/filters'
import { MemberManagement } from './components/members'
import { Trash2, RotateCcw } from 'lucide-react'

import './styles/global.css'
import './components/layout/layout.css'

// ============================================================================
// Smart List Views
// ============================================================================

function PriorityView({ tasks, onCompleteTask, onStarTask, onEditTask, onDeleteTask, onMoveTask, getAvailableLists, getProjectTags, onAddTag, onRemoveTag, onCreateTag, onSetDueDate, onAssignTask, onUnassignTask, getProjectMembers, allProjectTags = {}, allProjectMembers = [] }) {
  const [sortBy, setSortBy] = useState('created-desc')
  const [selectedUserIds, setSelectedUserIds] = useState([])
  const [selectedTagIds, setSelectedTagIds] = useState([])

  const filteredTasks = useMemo(() => {
    let result = [...tasks]
    if (selectedUserIds.length > 0) {
      result = result.filter(t => t.assignees && t.assignees.some(userId => selectedUserIds.includes(userId)))
    }
    if (selectedTagIds.length > 0) {
      result = result.filter(t => {
        if (!t.tags || t.tags.length === 0) return false
        const projectTags = getProjectTags(t.projectId)
        return t.tags.some(tagId => { const tag = projectTags[tagId]; return tag && selectedTagIds.includes(tag.name) })
      })
    }
    result.sort((a, b) => {
      if (sortBy === 'due-date') {
        if (!a.dueDate && !b.dueDate) return 0; if (!a.dueDate) return 1; if (!b.dueDate) return -1
        return new Date(a.dueDate.year, a.dueDate.month - 1, a.dueDate.day) - new Date(b.dueDate.year, b.dueDate.month - 1, b.dueDate.day)
      }
      if (sortBy === 'created-asc') return (a.id || 0) - (b.id || 0)
      return (b.id || 0) - (a.id || 0)
    })
    return result
  }, [tasks, selectedUserIds, selectedTagIds, sortBy, getProjectTags])

  if (tasks.length === 0) return <EmptyState icon={Star} message="No priority tasks. Star a task to add it here." />

  return (
    <div className="project-view">
      <ProjectHeader title="Priority" icon={Star} showNotes={false} rightAction={
        <FilterBar sortBy={sortBy} onSortChange={setSortBy} allMembers={allProjectMembers} selectedUserIds={selectedUserIds} onUserFilterChange={setSelectedUserIds} allTags={allProjectTags} selectedTagIds={selectedTagIds} onTagFilterChange={setSelectedTagIds} showUserFilter={allProjectMembers.length > 0} showTagFilter={Object.keys(allProjectTags).length > 0} />
      } />
      {filteredTasks.length === 0 ? <EmptyState icon={Star} message="No tasks match the current filters." /> : (
      <div className="project-view__section">
        {filteredTasks.map(task => (
          <TaskItem key={`${task.projectId}-${task.id}`} taskId={task.id} task={task} projectName={task.listName} showProject={true}
            onComplete={(id, completed) => onCompleteTask(task.projectId, id, completed)}
            onStar={(id, starred) => onStarTask(task.projectId, id, starred)}
            onEdit={(id, title, notes) => onEditTask(task.projectId, id, title, notes)}
            onDelete={(id) => onDeleteTask(task.projectId, id)}
            onMove={(id, listId) => onMoveTask(task.projectId, id, listId)}
            availableLists={getAvailableLists(task.projectId)}
            allTags={getProjectTags(task.projectId)}
            onAddTag={(id, tagId) => onAddTag(task.projectId, id, tagId)}
            onRemoveTag={(id, tagId) => onRemoveTag(task.projectId, id, tagId)}
            onCreateTag={(name) => onCreateTag(task.projectId, name)}
            onSetDueDate={(id, date) => onSetDueDate(task.projectId, id, date)}
            allMembers={getProjectMembers ? getProjectMembers(task.projectId) : []}
            onAssign={onAssignTask ? (id, userId) => onAssignTask(task.projectId, id, userId) : undefined}
            onUnassign={onUnassignTask ? (id, userId) => onUnassignTask(task.projectId, id, userId) : undefined}
          />
        ))}
      </div>)}
    </div>
  )
}

function LogbookView({ tasks, onCompleteTask, onStarTask, getProjectTags, getProjectMembers }) {
  if (tasks.length === 0) return <EmptyState icon={CheckSquare} message="No completed tasks yet." />
  return (
    <div className="project-view">
      <ProjectHeader title="Logbook" icon={CheckSquare} showNotes={false} />
      <div className="project-view__section">
        {tasks.map(task => (
          <TaskItem key={`${task.projectId}-${task.id}`} taskId={task.id} task={task} projectName={task.listName} showProject={true}
            onComplete={(id, completed) => onCompleteTask(task.projectId, id, completed)}
            onStar={(id, starred) => onStarTask(task.projectId, id, starred)}
            onEdit={() => {}} onDelete={() => {}} onMove={() => {}}
            availableLists={[]} allTags={getProjectTags(task.projectId)}
            allMembers={getProjectMembers ? getProjectMembers(task.projectId) : []}
          />
        ))}
      </div>
    </div>
  )
}

function TrashView({ tasks, onRestoreTask }) {
  if (tasks.length === 0) return <EmptyState icon={Trash2} message="Trash is empty." />
  return (
    <div className="project-view">
      <ProjectHeader title="Trash" icon={Trash2} showNotes={false} />
      <div className="project-view__section">
        {tasks.map(task => (
          <div key={`${task.projectId}-${task.id}`} className="trash-item">
            <div className="trash-item__content">
              <span className="trash-item__title">{task.title}</span>
              <span className="trash-item__meta">{task.listName}</span>
            </div>
            {task.canRestore !== false ? (
              <button className="trash-item__restore" onClick={() => onRestoreTask(task.projectId, task.id)} title="Restore task">
                <RotateCcw size={16} /> Restore
              </button>
            ) : <span className="trash-item__disabled" title="Cannot restore - list has been deleted">Cannot restore</span>}
          </div>
        ))}
      </div>
    </div>
  )
}

function AllTasksView({ tasks, onCompleteTask, onStarTask, onEditTask, onDeleteTask, onMoveTask, getAvailableLists, getProjectTags, onAddTag, onRemoveTag, onCreateTag, onSetDueDate, onAssignTask, onUnassignTask, getProjectMembers, allProjectTags = {}, allProjectMembers = [], projects = [], onNavigateToList }) {
  const [sortBy, setSortBy] = useState('created-desc')
  const [selectedUserIds, setSelectedUserIds] = useState([])
  const [selectedTagIds, setSelectedTagIds] = useState([])

  const filteredTasks = useMemo(() => {
    let result = [...tasks]
    if (selectedUserIds.length > 0) result = result.filter(t => t.assignees && t.assignees.some(userId => selectedUserIds.includes(userId)))
    if (selectedTagIds.length > 0) {
      result = result.filter(t => {
        if (!t.tags || t.tags.length === 0) return false
        const projectTags = getProjectTags(t.projectId)
        return t.tags.some(tagId => { const tag = projectTags[tagId]; return tag && selectedTagIds.includes(tag.name) })
      })
    }
    result.sort((a, b) => {
      if (sortBy === 'due-date') {
        if (!a.dueDate && !b.dueDate) return 0; if (!a.dueDate) return 1; if (!b.dueDate) return -1
        return new Date(a.dueDate.year, a.dueDate.month - 1, a.dueDate.day) - new Date(b.dueDate.year, b.dueDate.month - 1, b.dueDate.day)
      }
      if (sortBy === 'created-asc') return (a.id || 0) - (b.id || 0)
      return (b.id || 0) - (a.id || 0)
    })
    return result
  }, [tasks, selectedUserIds, selectedTagIds, sortBy, getProjectTags])

  if (tasks.length === 0) return <EmptyState icon={Circle} message="No tasks yet. Create a task in a project to see it here." />

  return (
    <div className="project-view">
      <ProjectHeader title="All Tasks" icon={Circle} showNotes={false} rightAction={
        <FilterBar sortBy={sortBy} onSortChange={setSortBy} allMembers={allProjectMembers} selectedUserIds={selectedUserIds} onUserFilterChange={setSelectedUserIds} allTags={allProjectTags} selectedTagIds={selectedTagIds} onTagFilterChange={setSelectedTagIds} showUserFilter={allProjectMembers.length > 0} showTagFilter={Object.keys(allProjectTags).length > 0} />
      } />
      {filteredTasks.length === 0 ? <EmptyState icon={Circle} message="No tasks match the current filters." /> : (
      <div className="project-view__section">
        {filteredTasks.map(task => {
          const project = projects.find(p => p.id === task.projectId)
          const projectName = project?.name || ''
          const locationPath = projectName && task.listName ? `${projectName}/${task.listName}` : task.listName
          return (
            <TaskItem key={`${task.projectId}-${task.id}`} taskId={task.id} task={task} locationPath={locationPath}
              onNavigateToLocation={() => onNavigateToList?.(task.projectId, task.listId)}
              onComplete={(id, completed) => onCompleteTask(task.projectId, id, completed)}
              onStar={(id, starred) => onStarTask(task.projectId, id, starred)}
              onEdit={(id, title, notes) => onEditTask(task.projectId, id, title, notes)}
              onDelete={(id) => onDeleteTask(task.projectId, id)}
              onMove={(id, listId) => onMoveTask(task.projectId, id, listId)}
              availableLists={getAvailableLists(task.projectId)}
              allTags={getProjectTags(task.projectId)}
              onAddTag={(id, tagId) => onAddTag(task.projectId, id, tagId)}
              onRemoveTag={(id, tagId) => onRemoveTag(task.projectId, id, tagId)}
              onCreateTag={(name) => onCreateTag(task.projectId, name)}
              onSetDueDate={(id, date) => onSetDueDate(task.projectId, id, date)}
              allMembers={getProjectMembers ? getProjectMembers(task.projectId) : []}
              onAssign={onAssignTask ? (id, userId) => onAssignTask(task.projectId, id, userId) : undefined}
              onUnassign={onUnassignTask ? (id, userId) => onUnassignTask(task.projectId, id, userId) : undefined}
            />
          )
        })}
      </div>)}
    </div>
  )
}

// ============================================================================
// Project View
// ============================================================================

function ProjectView({ project, model, userId, dispatch, filterTab, onFilterChange, onRenameList, onDeleteList, onMoveList, otherProjects, onMoveListToProject, members, selectedListId, onRenameProject, onAddList, onDeleteTask }) {
  const [listCollapseState, setListCollapseState] = useState(new Map())
  const [showAddListForm, setShowAddListForm] = useState(false)
  const [newListName, setNewListName] = useState('')
  const [sortBy, setSortBy] = useState('created-desc')
  const [selectedUserIds, setSelectedUserIds] = useState([])
  const [selectedTagIds, setSelectedTagIds] = useState([])

  const handleAddListSubmit = (e) => {
    e.preventDefault()
    if (newListName.trim() && onAddList) { onAddList(newListName.trim()); setNewListName(''); setShowAddListForm(false) }
  }

  const allLists = useMemo(() => {
    if (!model) return []
    return getLists(model).map(id => ({ id, name: getListName(model, id) || '' }))
  }, [model])

  const lists = useMemo(() => {
    if (selectedListId !== null) return allLists.filter(l => l.id === selectedListId)
    return allLists
  }, [allLists, selectedListId])

  const allTags = useMemo(() => model ? model.tags : {}, [model])

  const getTasksForList = useCallback((listId) => {
    if (!model) return []
    const taskIds = getTasksInList(model, listId)
    let tasks = taskIds.map(id => ({ id, ...getTask(model, id) })).filter(t => !t.deleted)
      .filter(t => {
        if (filterTab === 'logbook') return t.completed
        if (filterTab === 'important') return t.starred && !t.completed
        return !t.completed
      })
    if (selectedUserIds.length > 0) tasks = tasks.filter(t => t.assignees && t.assignees.some(userId => selectedUserIds.includes(userId)))
    if (selectedTagIds.length > 0) tasks = tasks.filter(t => t.tags && t.tags.some(tagId => selectedTagIds.includes(tagId)))
    tasks.sort((a, b) => {
      if (sortBy === 'due-date') {
        if (!a.dueDate && !b.dueDate) return 0; if (!a.dueDate) return 1; if (!b.dueDate) return -1
        return new Date(a.dueDate.year, a.dueDate.month - 1, a.dueDate.day) - new Date(b.dueDate.year, b.dueDate.month - 1, b.dueDate.day)
      }
      if (sortBy === 'created-asc') return (a.id || 0) - (b.id || 0)
      return (b.id || 0) - (a.id || 0)
    })
    return tasks
  }, [model, filterTab, selectedUserIds, selectedTagIds, sortBy])

  const isListCollapsed = useCallback((listId, taskCount) => {
    if (listCollapseState.has(listId)) return listCollapseState.get(listId)
    return taskCount === 0
  }, [listCollapseState])

  const toggleCollapse = (listId, taskCount) => {
    setListCollapseState(prev => { const next = new Map(prev); next.set(listId, !isListCollapsed(listId, taskCount)); return next })
  }

  if (!model) return <LoadingState message="Loading project..." />

  const priorityCount = countPriorityTasks(model)

  return (
    <div className="project-view">
      <ProjectHeader title={project.name} icon={Circle} subtitle={project.isOwner ? 'Owner' : 'Member'} showNotes={false} canRename={project.isOwner} onRename={onRenameProject} rightAction={
        <FilterBar sortBy={sortBy} onSortChange={setSortBy} allMembers={members} selectedUserIds={selectedUserIds} onUserFilterChange={setSelectedUserIds} allTags={allTags} selectedTagIds={selectedTagIds} onTagFilterChange={setSelectedTagIds} showUserFilter={members.length > 0} showTagFilter={Object.keys(allTags).length > 0} showDueDateSort={filterTab !== 'logbook'} />
      } />
      <FilterTabs
        tabs={[
          { id: 'all', label: 'All' },
          { id: 'important', label: `Priority${priorityCount > 0 ? ` (${priorityCount})` : ''}` },
          { id: 'logbook', label: 'Logbook' }
        ]}
        activeTab={filterTab} onTabChange={onFilterChange}
        onAddList={onAddList ? () => setShowAddListForm(true) : undefined}
      />
      {showAddListForm && (
        <form className="project-view__add-list-form" onSubmit={handleAddListSubmit}>
          <input type="text" placeholder="List name..." value={newListName} onChange={(e) => setNewListName(e.target.value)} autoFocus
            onKeyDown={(e) => { if (e.key === 'Escape') { setNewListName(''); setShowAddListForm(false) } }} />
          <button type="submit" disabled={!newListName.trim()}>Add</button>
          <button type="button" onClick={() => { setNewListName(''); setShowAddListForm(false) }}>Cancel</button>
        </form>
      )}
      {lists.length === 0 ? <EmptyState message={selectedListId !== null ? "List not found" : "No lists yet. Click '+ Add List' above."} /> :
        lists.map(list => {
          const tasks = getTasksForList(list.id)
          return (
          <TaskList key={list.id} listId={list.id} listName={list.name} tasks={tasks}
            collapsed={isListCollapsed(list.id, tasks.length)} onToggleCollapse={() => toggleCollapse(list.id, tasks.length)}
            onAddTask={(listId, title) => dispatch({ kind: 'AddTask', listId, title })}
            onRenameList={onRenameList} onDeleteList={onDeleteList} onMoveList={onMoveList}
            allLists={allLists} otherProjects={otherProjects} onMoveListToProject={onMoveListToProject}
            onCompleteTask={(taskId, completed) => dispatch(completed ? { kind: 'CompleteTask', taskId } : { kind: 'UncompleteTask', taskId })}
            onStarTask={(taskId, starred) => dispatch(starred ? { kind: 'StarTask', taskId } : { kind: 'UnstarTask', taskId })}
            onEditTask={(taskId, title, notes) => dispatch({ kind: 'EditTask', taskId, title, notes })}
            onDeleteTask={onDeleteTask}
            onMoveTask={(taskId, toListId) => dispatch({ kind: 'MoveTask', taskId, toList: toListId, taskPlace: { kind: 'AtEnd' } })}
            availableLists={allLists} allTags={allTags}
            onAddTag={(taskId, tagId) => dispatch({ kind: 'AddTagToTask', taskId, tagId })}
            onRemoveTag={(taskId, tagId) => dispatch({ kind: 'RemoveTagFromTask', taskId, tagId })}
            onCreateTag={(name) => dispatch({ kind: 'CreateTag', name })}
            onSetDueDate={(taskId, date) => {
              if (date) dispatch({ kind: 'SetDueDate', taskId, dueDate: { year: date.year, month: date.month, day: date.day } })
              else dispatch({ kind: 'SetDueDate', taskId })
            }}
            allMembers={members}
            onAssign={(taskId, userId) => dispatch({ kind: 'AssignTask', taskId, userId })}
            onUnassign={(taskId, userId) => dispatch({ kind: 'UnassignTask', taskId, userId })}
          />)
        })
      }
    </div>
  )
}

// ============================================================================
// Main Todo App
// ============================================================================

function TodoApp({ user, onSignOut }) {
  const [selectedView, setSelectedView] = useState(null)
  const [selectedProjectId, setSelectedProjectId] = useState(null)
  const [selectedListId, setSelectedListId] = useState(null)
  const [filterTab, setFilterTab] = useState('all')
  const [toast, setToast] = useState(null)
  const [showMemberManagement, setShowMemberManagement] = useState(false)
  const [isSidebarOpen, setIsSidebarOpen] = useState(false)
  const [pendingUndo, setPendingUndo] = useState(null)

  useEffect(() => {
    const handleResize = () => { if (window.innerWidth > 768) setIsSidebarOpen(false) }
    window.addEventListener('resize', handleResize)
    return () => window.removeEventListener('resize', handleResize)
  }, [])

  useEffect(() => {
    const handleKeyDown = (e) => { if (e.key === 'Escape' && isSidebarOpen) setIsSidebarOpen(false) }
    window.addEventListener('keydown', handleKeyDown)
    return () => window.removeEventListener('keydown', handleKeyDown)
  }, [isSidebarOpen])

  const { projects, loading: projectsLoading, createProject, renameProject, deleteProject } = useProjects(user?.id)

  const projectIds = useMemo(() => projects.map(p => p.id), [projects])
  const {
    createDispatch, priorityTasks, logbookTasks, allTasks, trashTasks,
    getProjectModel, getProjectLists, getListTaskCount, getProjectMembers,
    moveListToProject, refresh: sync, error, status, isOffline, hasPending: isFlushing
  } = useAllProjects(projectIds)

  useEffect(() => {
    if (projects.length === 0) return
    const savedId = localStorage.getItem('collab-todo:selectedProjectId')
    if (savedId && projects.find(p => p.id === savedId)) setSelectedProjectId(savedId)
  }, [projects])

  useEffect(() => { if (selectedProjectId) localStorage.setItem('collab-todo:selectedProjectId', selectedProjectId) }, [selectedProjectId])

  const singleModel = selectedProjectId ? getProjectModel(selectedProjectId) : null
  const singleDispatch = useMemo(() => selectedProjectId ? createDispatch(selectedProjectId) : () => {}, [selectedProjectId, createDispatch])

  const { members, inviteMember, removeMember: removeFromSupabase, refresh: refreshMembers } = useProjectMembers(selectedProjectId)

  const projectMode = singleModel ? singleModel.mode : null
  const projectOwner = singleModel ? singleModel.owner : null

  useEffect(() => { if (error) setToast({ message: error, type: 'error' }) }, [error])

  const handleSelectProject = (projectId) => { setSelectedProjectId(projectId); setSelectedListId(null); setSelectedView(null); setShowMemberManagement(false) }
  const handleSelectList = (projectId, listId) => { setSelectedProjectId(projectId); setSelectedListId(listId); setSelectedView(null); setShowMemberManagement(false) }
  const handleSelectView = (view) => { setSelectedView(view); setSelectedListId(null); setShowMemberManagement(false) }
  const handleManageMembers = (projectId) => { setSelectedProjectId(projectId); setSelectedView(null); setSelectedListId(null); setShowMemberManagement(true) }

  const handleAddList = (name) => { if (selectedProjectId) singleDispatch({ kind: 'AddList', name }) }
  const handleRenameList = (listId, newName) => { if (selectedProjectId) singleDispatch({ kind: 'RenameList', listId, newName }) }
  const handleDeleteList = (listId) => { if (selectedProjectId && confirm('Delete this list? All tasks in it will be permanently deleted.')) singleDispatch({ kind: 'DeleteList', listId }) }
  const handleRenameProject = async (newName) => { if (selectedProjectId) { try { await renameProject(selectedProjectId, newName) } catch (err) { console.error('Failed to rename project:', err) } } }
  const handleMoveList = (listId, anchorId, direction) => {
    const listPlace = direction === 'before' ? { kind: 'ListBefore', anchor: anchorId } : { kind: 'ListAfter', anchor: anchorId }
    singleDispatch({ kind: 'MoveList', listId, listPlace })
  }
  const handleMoveListToProject = (listId, targetProjectId) => { if (selectedProjectId) moveListToProject(selectedProjectId, targetProjectId, listId) }

  const handleMakeCollaborative = () => { singleDispatch({ kind: 'MakeCollaborative' }) }
  const handleInviteMember = async (email) => {
    const userId = await inviteMember(email)
    if (userId) singleDispatch({ kind: 'AddMember', userId })
    await refreshMembers()
  }
  const handleRemoveMember = async (userId) => {
    await removeFromSupabase(userId)
    singleDispatch({ kind: 'RemoveMember', userId })
    await refreshMembers()
  }

  const handleCreateProject = async (name) => { const projectId = await createProject(name); setSelectedProjectId(projectId); setSelectedView(null); return projectId }
  const handleDeleteProject = async (projectId) => {
    try {
      await deleteProject(projectId)
      if (selectedProjectId === projectId) { setSelectedProjectId(null); setSelectedListId(null); localStorage.removeItem('collab-todo:selectedProjectId') }
      setToast({ message: 'Project deleted', type: 'success' })
    } catch (err) { console.error('Failed to delete project:', err); setToast({ message: err.message || 'Failed to delete project', type: 'error' }) }
  }

  const handleCompleteTaskAll = (projectId, taskId, completed) => { createDispatch(projectId)(completed ? { kind: 'CompleteTask', taskId } : { kind: 'UncompleteTask', taskId }) }
  const handleStarTaskAll = (projectId, taskId, starred) => { createDispatch(projectId)(starred ? { kind: 'StarTask', taskId } : { kind: 'UnstarTask', taskId }) }
  const handleEditTaskAll = (projectId, taskId, title, notes) => { createDispatch(projectId)({ kind: 'EditTask', taskId, title, notes }) }
  const handleDeleteTaskAll = (projectId, taskId) => {
    const model = getProjectModel(projectId)
    const task = model ? getTask(model, taskId) : null
    const taskTitle = task?.title || 'Task'
    createDispatch(projectId)({ kind: 'DeleteTask', taskId, userId: user.id })
    setPendingUndo({ projectId, taskId, taskTitle })
  }
  const handleRestoreTask = (projectId, taskId) => { createDispatch(projectId)({ kind: 'RestoreTask', taskId }); setPendingUndo(null) }
  const handleMoveTaskAll = (projectId, taskId, listId) => { createDispatch(projectId)({ kind: 'MoveTask', taskId, toList: listId, taskPlace: { kind: 'AtEnd' } }) }
  const handleAddTagAll = (projectId, taskId, tagId) => { createDispatch(projectId)({ kind: 'AddTagToTask', taskId, tagId }) }
  const handleRemoveTagAll = (projectId, taskId, tagId) => { createDispatch(projectId)({ kind: 'RemoveTagFromTask', taskId, tagId }) }
  const handleCreateTagAll = (projectId, name) => { createDispatch(projectId)({ kind: 'CreateTag', name }) }
  const handleSetDueDateAll = (projectId, taskId, date) => {
    if (date) createDispatch(projectId)({ kind: 'SetDueDate', taskId, dueDate: { year: date.year, month: date.month, day: date.day } })
    else createDispatch(projectId)({ kind: 'SetDueDate', taskId })
  }
  const handleAssignTaskAll = (projectId, taskId, userId) => { createDispatch(projectId)({ kind: 'AssignTask', taskId, userId }) }
  const handleUnassignTaskAll = (projectId, taskId, userId) => { createDispatch(projectId)({ kind: 'UnassignTask', taskId, userId }) }

  const getProjectTags = useCallback((projectId) => {
    const model = getProjectModel(projectId)
    return model ? model.tags : {}
  }, [getProjectModel])

  const allProjectTags = useMemo(() => {
    const byName = new Map()
    projects.forEach(project => {
      const tags = getProjectTags(project.id)
      Object.entries(tags).forEach(([id, tag]) => { if (!byName.has(tag.name)) byName.set(tag.name, { ...tag }) })
    })
    const aggregated = {}
    byName.forEach((tag, name) => { aggregated[name] = tag })
    return aggregated
  }, [projects, getProjectTags])

  const allProjectMembers = useMemo(() => {
    const memberMap = new Map()
    projects.forEach(project => {
      const pm = getProjectMembers(project.id)
      if (pm) pm.forEach(member => { if (!memberMap.has(member.user_id)) memberMap.set(member.user_id, member) })
    })
    return Array.from(memberMap.values())
  }, [projects, getProjectMembers])

  const priorityCount = priorityTasks.length
  const logbookCount = logbookTasks.length
  const allTasksCount = allTasks.length
  const trashCount = trashTasks.length

  const getProjectMode = useCallback((projectId) => {
    const model = getProjectModel(projectId)
    return model ? model.mode : null
  }, [getProjectModel])

  const renderContent = () => {
    if (showMemberManagement && selectedProjectId) {
      const project = projects.find(p => p.id === selectedProjectId)
      if (!project) return <EmptyState message="Project not found" />
      return <MemberManagement projectName={project.name} projectMode={projectMode} members={members} ownerId={projectOwner} isOwner={project.isOwner} onMakeCollaborative={handleMakeCollaborative} onInviteMember={handleInviteMember} onRemoveMember={handleRemoveMember} onBack={() => setShowMemberManagement(false)} />
    }
    if (selectedView === 'allTasks') return <AllTasksView tasks={allTasks} onCompleteTask={handleCompleteTaskAll} onStarTask={handleStarTaskAll} onEditTask={handleEditTaskAll} onDeleteTask={handleDeleteTaskAll} onMoveTask={handleMoveTaskAll} getAvailableLists={getProjectLists} getProjectTags={getProjectTags} onAddTag={handleAddTagAll} onRemoveTag={handleRemoveTagAll} onCreateTag={handleCreateTagAll} onSetDueDate={handleSetDueDateAll} onAssignTask={handleAssignTaskAll} onUnassignTask={handleUnassignTaskAll} getProjectMembers={getProjectMembers} allProjectTags={allProjectTags} allProjectMembers={allProjectMembers} projects={projects} onNavigateToList={handleSelectList} />
    if (selectedView === 'priority') return <PriorityView tasks={priorityTasks} onCompleteTask={handleCompleteTaskAll} onStarTask={handleStarTaskAll} onEditTask={handleEditTaskAll} onDeleteTask={handleDeleteTaskAll} onMoveTask={handleMoveTaskAll} getAvailableLists={getProjectLists} getProjectTags={getProjectTags} onAddTag={handleAddTagAll} onRemoveTag={handleRemoveTagAll} onCreateTag={handleCreateTagAll} onSetDueDate={handleSetDueDateAll} onAssignTask={handleAssignTaskAll} onUnassignTask={handleUnassignTaskAll} getProjectMembers={getProjectMembers} allProjectTags={allProjectTags} allProjectMembers={allProjectMembers} />
    if (selectedView === 'logbook') return <LogbookView tasks={logbookTasks} onCompleteTask={handleCompleteTaskAll} onStarTask={handleStarTaskAll} getProjectTags={getProjectTags} getProjectMembers={getProjectMembers} />
    if (selectedView === 'trash') return <TrashView tasks={trashTasks} onRestoreTask={handleRestoreTask} />
    if (selectedProjectId) {
      const project = projects.find(p => p.id === selectedProjectId)
      if (!project) return <EmptyState message="Project not found" />
      return <ProjectView project={project} model={singleModel} userId={user.id} dispatch={singleDispatch} filterTab={filterTab} onFilterChange={setFilterTab} onRenameList={handleRenameList} onDeleteList={handleDeleteList} onMoveList={handleMoveList} otherProjects={projects.filter(p => p.id !== selectedProjectId)} onMoveListToProject={project.isOwner ? handleMoveListToProject : undefined} members={members} selectedListId={selectedListId} onRenameProject={project.isOwner ? handleRenameProject : undefined} onAddList={handleAddList} onDeleteTask={(taskId) => handleDeleteTaskAll(selectedProjectId, taskId)} />
    }
    return <EmptyState message="Select a project or smart list to get started" />
  }

  const toggleSidebar = useCallback(() => { setIsSidebarOpen(prev => !prev) }, [])
  const closeSidebar = useCallback(() => { setIsSidebarOpen(false) }, [])

  return (
    <div className="app-layout">
      <TopBar user={user} onSignOut={onSignOut} onSync={sync} isOffline={isOffline} isFlushing={isFlushing} status={status} onToggleSidebar={toggleSidebar} isSidebarOpen={isSidebarOpen} />
      <div className="content-wrapper" style={isOffline ? { pointerEvents: 'none', opacity: 0.5 } : undefined}>
        <div className={`sidebar-overlay ${isSidebarOpen ? 'sidebar-overlay--visible' : ''}`} onClick={closeSidebar} aria-hidden="true" />
        <Sidebar selectedView={selectedView} onSelectView={handleSelectView} projects={projects} selectedProjectId={selectedProjectId} selectedListId={selectedListId} onSelectProject={handleSelectProject} onSelectList={handleSelectList} onCreateProject={handleCreateProject} onAddList={handleAddList} projectsLoading={projectsLoading} getProjectLists={getProjectLists} getListTaskCount={getListTaskCount} priorityCount={priorityCount} logbookCount={logbookCount} allTasksCount={allTasksCount} trashCount={trashCount} onManageMembers={handleManageMembers} onDeleteProject={handleDeleteProject} getProjectMode={getProjectMode} isOpen={isSidebarOpen} onClose={closeSidebar} />
        <MainContent>{renderContent()}</MainContent>
      </div>
      {toast && <Toast message={toast.message} type={toast.type} onClose={() => setToast(null)} />}
      {pendingUndo && <UndoToast message={`"${pendingUndo.taskTitle}" deleted`} onUndo={() => handleRestoreTask(pendingUndo.projectId, pendingUndo.taskId)} onClose={() => setPendingUndo(null)} />}
      {isOffline && <div className="offline-overlay"><div className="offline-overlay__content"><h2>You are offline</h2><p>Please reconnect to the internet to continue using the app.</p></div></div>}
      <Footer />
    </div>
  )
}

// ============================================================================
// App Container (Auth wrapper)
// ============================================================================

function AppContainer() {
  const [user, setUser] = useState(null)
  const [loading, setLoading] = useState(true)

  useEffect(() => {
    if (!isBackendConfigured()) { setLoading(false); return }
    const unsubscribe = backend.auth.onAuthChange((user) => { setUser(user); setLoading(false) })
    return () => unsubscribe()
  }, [])

  const handleSignOut = async () => { await signOut() }

  if (loading) return <div className="auth-container"><h1 className="auth-container__title">Todo</h1><p className="auth-container__subtitle">Loading...</p><Footer /></div>
  if (!user) return <div className="auth-container"><h1 className="auth-container__title">Todo</h1><p className="auth-container__subtitle">Collaborative task management</p><AuthForm /><Footer /></div>
  return <TodoApp user={user} onSignOut={handleSignOut} />
}

export default AppContainer
