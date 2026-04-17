// MultiProjectEffectManager: drives the verified effect state machine from domain.ts
// Only handles I/O (network calls, browser events). All state transitions go through step().

import { backend, isBackendConfigured } from '../backend/index.ts'
import { step, initEffect } from '../domain.ts'

export class MultiProjectEffectManager {
  #state = null           // EffectState from domain.ts
  #projectIds = []
  #listeners = new Set()
  #realtimeUnsubscribers = []
  #statusCallback = null
  #errorCallback = null

  constructor(projectIds = []) {
    this.#projectIds = projectIds
  }

  // useSyncExternalStore protocol
  subscribe = (listener) => {
    this.#listeners.add(listener)
    return () => this.#listeners.delete(listener)
  }

  getSnapshot = () => {
    return this.#state ? this.#state.client.present : null
  }

  getBaseVersions = () => {
    return this.#state ? this.#state.client.baseVersions : {}
  }

  #notify() { this.#listeners.forEach(l => l()) }

  setCallbacks(statusCallback, errorCallback) {
    this.#statusCallback = statusCallback
    this.#errorCallback = errorCallback
  }

  #setStatus(status) { this.#statusCallback?.(status) }
  #setError(error) { this.#errorCallback?.(error) }

  // Transition via VERIFIED step function
  #transition(event) {
    if (!this.#state) return null
    const result = step(this.#state, event)
    this.#state = result.state
    this.#notify()
    return result.command
  }

  // Execute command returned by step (I/O only)
  async #executeCommand(command) {
    if (command.kind === 'CmdNoOp') return

    if (command.kind === 'SendDispatch') {
      this.#setStatus('pending')
      try {
        const { touchedProjects, baseVersions, action } = command
        const isSingleProject = action.kind === 'SingleAction' && touchedProjects.length === 1

        let response
        if (isSingleProject) {
          const projectId = touchedProjects[0]
          const data = await backend.dispatch.single(
            projectId,
            baseVersions[projectId] || 0,
            action.action
          )
          if (data.status === 'accepted') {
            response = {
              status: 'accepted',
              versions: { [projectId]: data.version },
              states: { [projectId]: data.state }
            }
          } else {
            response = data
          }
        } else {
          response = await backend.dispatch.multi(baseVersions, action)
        }

        let event
        if (response.status === 'accepted') {
          event = { kind: 'DispatchAccepted', newVersions: response.versions, newModels: response.states }
          this.#setStatus('synced')
          this.#setError(null)
        } else if (response.status === 'conflict') {
          const freshVersions = {}, freshStates = {}
          for (const projectId of touchedProjects) {
            try {
              const { state, version } = await backend.projects.load(projectId)
              freshVersions[projectId] = version
              freshStates[projectId] = state
            } catch (e) { console.error(`Failed to load project ${projectId}:`, e) }
          }
          event = { kind: 'DispatchConflict', freshVersions, freshModels: freshStates }
        } else if (response.status === 'rejected') {
          const freshVersions = {}, freshStates = {}
          for (const projectId of touchedProjects) {
            try {
              const { state, version } = await backend.projects.load(projectId)
              freshVersions[projectId] = version
              freshStates[projectId] = state
            } catch (e) { console.error(`Failed to load project ${projectId}:`, e) }
          }
          event = { kind: 'DispatchRejected', freshVersions, freshModels: freshStates }
          this.#setError(`Action rejected: ${response.error || 'Unknown'}`)
        }

        if (event) {
          const nextCmd = this.#transition(event)
          if (nextCmd) await this.#executeCommand(nextCmd)
        }
      } catch (e) {
        console.error('Dispatch error:', e)
        if (e.message?.includes('fetch') || e.message?.includes('network') || !navigator.onLine) {
          this.#transition({ kind: 'NetworkError' })
          this.#setStatus('offline')
          this.#setError(null)
        } else {
          // Fetch fresh state and reject — must transition effect machine out of Dispatching
          const freshVersions = {}, freshStates = {}
          for (const projectId of this.#projectIds) {
            try {
              const { state, version } = await backend.projects.load(projectId)
              freshVersions[projectId] = version
              freshStates[projectId] = state
            } catch (loadErr) { console.error(`Failed to load project ${projectId}:`, loadErr) }
          }
          const cmd = this.#transition({ kind: 'DispatchRejected', freshVersions, freshModels: freshStates })
          if (cmd) await this.#executeCommand(cmd)
          this.#setError(e.message)
          this.#setStatus('error')
        }
      }
    }
  }

  async start() {
    if (!isBackendConfigured() || this.#projectIds.length === 0) return
    this.#setStatus('syncing')
    try {
      const versions = {}, models = {}
      for (const projectId of this.#projectIds) {
        const { state, version } = await backend.projects.load(projectId)
        versions[projectId] = version
        models[projectId] = state
      }
      this.#state = initEffect(versions, models)
      this.#notify()
      this.#setStatus('synced')
      this.#setError(null)
      this.#subscribeRealtime()
      window.addEventListener('online', this.#handleOnline)
      window.addEventListener('offline', this.#handleOffline)
    } catch (e) {
      console.error('Sync error:', e)
      this.#setError(e.message)
      this.#setStatus('error')
    }
  }

  stop() {
    for (const unsubscribe of this.#realtimeUnsubscribers) unsubscribe()
    this.#realtimeUnsubscribers = []
    window.removeEventListener('online', this.#handleOnline)
    window.removeEventListener('offline', this.#handleOffline)
  }

  dispatchSingle(projectId, action) {
    if (!this.isOnline) { console.warn('Cannot dispatch while offline'); return }
    const multiAction = { kind: 'SingleAction', projectId, action }
    const cmd = this.#transition({ kind: 'UserAction', action: multiAction })
    if (cmd) this.#executeCommand(cmd)
  }

  dispatch(multiAction) {
    if (!this.isOnline) { console.warn('Cannot dispatch while offline'); return }
    const cmd = this.#transition({ kind: 'UserAction', action: multiAction })
    if (cmd) this.#executeCommand(cmd)
  }

  async sync() {
    if (!isBackendConfigured()) return
    if (this.#state && this.#state.mode.kind === 'Dispatching') {
      console.warn('Cannot sync while dispatching'); return
    }
    this.#setStatus('syncing')
    try {
      if (!this.#state) {
        const versions = {}, models = {}
        for (const projectId of this.#projectIds) {
          const { state, version } = await backend.projects.load(projectId)
          versions[projectId] = version
          models[projectId] = state
        }
        this.#state = initEffect(versions, models)
      } else {
        for (const projectId of this.#projectIds) {
          const { state, version } = await backend.projects.load(projectId)
          this.#transition({ kind: 'RealtimeUpdate', projectId, version, model: state })
        }
      }
      this.#notify()
      this.#setStatus('synced')
      this.#setError(null)
    } catch (e) {
      this.#setError(e.message)
      this.#setStatus('error')
    }
  }

  toggleOffline() {
    if (this.#state.network === 'Online') {
      this.#transition({ kind: 'ManualGoOffline' })
      this.#setStatus('offline')
      return true
    } else {
      const cmd = this.#transition({ kind: 'ManualGoOnline' })
      if (cmd) this.#executeCommand(cmd)
      return false
    }
  }

  #subscribeRealtime() {
    for (const projectId of this.#projectIds) this.#subscribeToProject(projectId)
  }

  #subscribeToProject(projectId) {
    const unsubscribe = backend.realtime.subscribe(projectId, (version, state) => {
      if (!this.#state || this.#state.network !== 'Online') return
      const serverVersion = this.#state.client.baseVersions[projectId] || 0
      if (version > serverVersion) {
        this.#transition({ kind: 'RealtimeUpdate', projectId, version, model: state })
      }
    })
    this.#realtimeUnsubscribers.push(unsubscribe)
  }

  #handleOnline = () => {
    const cmd = this.#transition({ kind: 'NetworkRestored' })
    if (cmd) this.#executeCommand(cmd)
  }

  #handleOffline = () => {
    this.#transition({ kind: 'NetworkError' })
    this.#setStatus('offline')
  }

  get isOnline() { return this.#state ? this.#state.network === 'Online' : true }
  get isDispatching() { return this.#state ? this.#state.mode.kind === 'Dispatching' : false }
  get hasPending() { return this.#state ? this.#state.client.pending.length > 0 : false }
  get pendingCount() { return this.#state ? this.#state.client.pending.length : 0 }
}
