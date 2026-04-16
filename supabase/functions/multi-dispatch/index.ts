// Supabase Edge Function: multi-dispatch
// Runs VERIFIED tryApplyMulti() for cross-project operations
// Atomically updates all touched projects with optimistic locking.

import { serve } from 'https://deno.land/std@0.168.0/http/server.ts'
import { createClient } from 'https://esm.sh/@supabase/supabase-js@2'
import { touchedProjects, tryApplyMulti } from '../../../src/domain.ts'

const corsHeaders = {
  'Access-Control-Allow-Origin': '*',
  'Access-Control-Allow-Methods': 'POST, OPTIONS',
  'Access-Control-Allow-Headers': 'authorization, content-type, x-client-info, apikey',
}

serve(async (req) => {
  if (req.method === 'OPTIONS') return new Response('ok', { headers: corsHeaders })

  try {
    const authHeader = req.headers.get('Authorization')
    if (!authHeader) {
      return new Response(JSON.stringify({ error: 'Missing Authorization header' }), {
        status: 401, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    const supabaseClient = createClient(
      Deno.env.get('SUPABASE_URL') ?? '',
      Deno.env.get('SUPABASE_ANON_KEY') ?? '',
      { global: { headers: { Authorization: authHeader } } }
    )

    const { data: { user }, error: authError } = await supabaseClient.auth.getUser()
    if (authError || !user) {
      return new Response(JSON.stringify({ error: 'Invalid or expired token' }), {
        status: 401, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    const { baseVersions, action } = await req.json() as { baseVersions: Record<string, number>; action: MultiAction }

    const projectIds = touchedProjects(action)
    if (projectIds.length === 0) {
      return new Response(JSON.stringify({ error: 'No projects touched by action' }), {
        status: 400, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Check membership for all touched projects
    const { data: memberships, error: memberError } = await supabaseClient
      .from('project_members').select('project_id')
      .eq('user_id', user.id).in('project_id', projectIds)

    if (memberError) {
      return new Response(JSON.stringify({ error: 'Failed to check membership' }), {
        status: 500, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    const memberProjectIds = new Set((memberships || []).map(m => m.project_id))
    const missingAccess = projectIds.filter(id => !memberProjectIds.has(id))
    if (missingAccess.length > 0) {
      return new Response(JSON.stringify({ error: 'Not a member of all touched projects', missingAccess }), {
        status: 403, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    const supabaseAdmin = createClient(
      Deno.env.get('SUPABASE_URL') ?? '',
      Deno.env.get('SUPABASE_SERVICE_ROLE_KEY') ?? ''
    )

    // Load touched projects
    const { data: projects, error: loadError } = await supabaseAdmin
      .from('projects').select('id, state, version').in('id', projectIds)

    if (loadError || !projects) {
      return new Response(JSON.stringify({ error: 'Failed to load projects' }), {
        status: 500, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Check versions match
    const projectMap: Record<string, { state: any; version: number }> = {}
    for (const p of projects) {
      projectMap[p.id] = { state: p.state, version: p.version }
      if (baseVersions[p.id] !== undefined && baseVersions[p.id] !== p.version) {
        return new Response(JSON.stringify({ status: 'conflict', message: 'Version mismatch' }), {
          status: 200, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
        })
      }
    }

    // Build MultiModel and run VERIFIED tryApplyMulti
    const mm: MultiModel = {
      projects: Object.fromEntries(Object.entries(projectMap).map(([id, p]) => [id, p.state]))
    }

    const newMM = tryApplyMulti(mm, action)

    // Check which projects changed
    const newVersions: Record<string, number> = {}
    const newStates: Record<string, any> = {}
    const changed: string[] = []

    for (const id of projectIds) {
      if (newMM.projects[id] !== mm.projects[id]) {
        changed.push(id)
        newVersions[id] = projectMap[id].version + 1
        newStates[id] = newMM.projects[id]
      }
    }

    if (changed.length === 0) {
      return new Response(JSON.stringify({ status: 'accepted', versions: {}, states: {} }), {
        status: 200, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Persist atomically
    for (const id of changed) {
      const { error: updateError } = await supabaseAdmin
        .from('projects')
        .update({ state: newStates[id], version: newVersions[id], updated_at: new Date().toISOString() })
        .eq('id', id).eq('version', projectMap[id].version)

      if (updateError) {
        return new Response(JSON.stringify({ status: 'conflict', message: 'Concurrent modification' }), {
          status: 409, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
        })
      }
    }

    return new Response(JSON.stringify({ status: 'accepted', versions: newVersions, states: newStates }), {
      status: 200, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
    })

  } catch (e) {
    console.error('Multi-dispatch error:', e)
    return new Response(JSON.stringify({ error: 'Internal error', details: String(e) }), {
      status: 500, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
    })
  }
})
