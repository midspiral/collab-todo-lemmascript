// Supabase Edge Function: dispatch
// Runs VERIFIED domain.ts apply() server-side
// Uses version-based optimistic locking; client effect machine handles conflicts.

import { serve } from 'https://deno.land/std@0.168.0/http/server.ts'
import { createClient } from 'https://esm.sh/@supabase/supabase-js@2'
import { apply } from '../../../src/domain.ts'

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

    const { projectId, baseVersion, action } = await req.json()

    if (!projectId) {
      return new Response(JSON.stringify({ error: 'projectId is required' }), {
        status: 400, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Check membership
    const { data: membership, error: memberError } = await supabaseClient
      .from('project_members').select('role')
      .eq('project_id', projectId).eq('user_id', user.id).single()

    if (memberError || !membership) {
      return new Response(JSON.stringify({ error: 'Not a member of this project' }), {
        status: 403, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Service role for writes
    const supabaseAdmin = createClient(
      Deno.env.get('SUPABASE_URL') ?? '',
      Deno.env.get('SUPABASE_SERVICE_ROLE_KEY') ?? ''
    )

    const { data: project, error: loadError } = await supabaseAdmin
      .from('projects').select('state, version')
      .eq('id', projectId).single()

    if (loadError || !project) {
      return new Response(JSON.stringify({ error: 'Project not found' }), {
        status: 404, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Version mismatch → conflict (client effect machine will fetch fresh state and retry)
    if (baseVersion !== project.version) {
      return new Response(JSON.stringify({ status: 'conflict', message: 'Version mismatch' }), {
        status: 200, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    // Run VERIFIED apply
    const result = apply(project.state, action)

    if (!result.ok) {
      return new Response(JSON.stringify({ status: 'rejected', reason: result.error }), {
        status: 200, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    const newVersion = project.version + 1

    // Optimistic lock write
    const { error: updateError } = await supabaseAdmin
      .from('projects')
      .update({ state: result.value, version: newVersion, updated_at: new Date().toISOString() })
      .eq('id', projectId)
      .eq('version', project.version)

    if (updateError) {
      return new Response(JSON.stringify({ status: 'conflict', message: 'Concurrent modification' }), {
        status: 409, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
      })
    }

    return new Response(JSON.stringify({ status: 'accepted', version: newVersion, state: result.value }), {
      status: 200, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
    })

  } catch (e) {
    console.error('Dispatch error:', e)
    return new Response(JSON.stringify({ error: 'Internal error', details: String(e) }), {
      status: 500, headers: { ...corsHeaders, 'Content-Type': 'application/json' }
    })
  }
})
