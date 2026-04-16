# Collab Todo (LemmaScript)

Collaborative task management app with a formally verified domain model.

The domain logic in `src/domain.ts` is written in TypeScript with [LemmaScript](https://github.com/midspiral/LemmaScript) annotations, verified through Dafny (131 lemmas, 0 errors). The same file is imported directly by the React UI, the React hooks, and the Supabase edge functions — no compilation step, no adapter layer.

This case study originally comes from [`metareflection/dafny-replay/collab-todo`](https://github.com/metareflection/dafny-replay/tree/main/collab-todo).
Here, the TypeScript is primary, and we generate a Dafny model using LemmaScript for verification, while there, the Dafny is primary, and we compiled to JavaScript for execution.

## Stack

- **Domain**: `src/domain.ts` — 25 single-project actions, 3 cross-project actions, effect state machine
- **Verification**: LemmaScript → Dafny, 85 verified functions + 131 proof lemmas
- **Frontend**: React 19, Vite
- **Backend**: Supabase (Auth, Postgres, Realtime, Edge Functions)

## Setup

### Prerequisites

- Node.js 20+
- [Dafny](https://github.com/dafny-lang/dafny) (for verification)
- [LemmaScript](https://github.com/midspiral/LemmaScript) as a sibling directory (`../LemmaScript`)
- A [Supabase](https://supabase.com) project

### Install

```bash
npm install
```

### Supabase

1. Create a Supabase project at [supabase.com](https://supabase.com)

2. Run the schema in the Supabase SQL editor:
   ```
   supabase/schema.sql
   ```

3. Create `.env` from the example:
   ```bash
   cp .env.example .env
   ```
   Fill in `VITE_SUPABASE_URL` and `VITE_SUPABASE_ANON_KEY` from your Supabase project settings.

   Find those values from your Supabase project dashboard:
   - Go to (Project) Settings > Data API
     - Note down Project URL (e.g., https://abcdefg.supabase.co)
   - Go to (Project) Settings > API Keys > Legacy anon, service_role API keys
     - Note down anon public key (starts with eyJ...)

4. Link and deploy edge functions:
   ```bash
   npx supabase login
   npx supabase link --project-ref <your-project-ref>
   npx supabase functions deploy dispatch
   npx supabase functions deploy multi-dispatch
   ```

### Run

```bash
npm run dev
```

## Verification

Requires `../LemmaScript` (midspiral/LemmaScript) as a sibling project.

### Verify domain logic (LemmaScript → Dafny)

```bash
../LemmaScript/tools/check.sh dafny
```

This regenerates `src/domain.dfy` from `src/domain.ts` via LemmaScript, then runs `dafny verify`. Expects 85 verified, 0 errors.

When making changes to the `src/domain.ts`, you can also regenerate the `dfy` from the generated `dfy.gen` using:
```bash
npx tsx ../LemmaScript/tools/src/lsc.ts regen --backend=dafny  src/domain.ts
```

### Verify proof lemmas

```bash
./check-extra.sh
```

Verifies `src/domain.proofs.dfy` — the proofs establishing the 16-conjunct invariant and its preservation across all actions (single-project, cross-project, and NoOp sanity). Expects 131 verified, 0 errors.

## Architecture

```
src/domain.ts          ← single source of truth (TypeScript + LemmaScript annotations)
  ├── src/domain.dfy        generated Dafny (lsc regen)
  ├── src/domain.proofs.dfy hand-written proofs
  ├── src/App.jsx            React UI (imports domain.ts directly)
  ├── src/hooks/             effect manager + React hooks (imports domain.ts directly)
  └── supabase/functions/    edge functions (imports domain.ts directly)
```

Actions are plain objects: `{ kind: 'AddTask', listId, title }`. No Dafny runtime, no BigNumber, no adapter layer.

## What's Verified

**16-conjunct invariant** on the Model (lists unique, task counts, allocator freshness, member/tag/title uniqueness, etc.) proven preserved by:

- All 25 single-project actions (`StepPreservesInv`)
- All 3 cross-project actions (`TryApplyMultiPreservesMultiInv`)
- NoOp soundness (`NoOpImpliesUnchanged`)
- Initialization (`InitSatisfiesInv`)

See `src/domain.proofs.dfy` for the full proof.
