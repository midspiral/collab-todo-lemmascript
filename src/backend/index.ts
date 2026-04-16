import { createSupabaseBackend } from './supabase'
import type { Backend } from './types'

export type { Backend, User, Project, ProjectState, Member, DispatchResult } from './types'

export const backend: Backend = createSupabaseBackend()

export const isBackendConfigured = (): boolean => backend.isConfigured

export const signIn = backend.auth.signIn
export const signUp = backend.auth.signUp
export const signInWithGoogle = backend.auth.signInWithGoogle
export const signOut = backend.auth.signOut
export const getSession = backend.auth.getCurrentUser
export const getAccessToken = backend.auth.getAccessToken
