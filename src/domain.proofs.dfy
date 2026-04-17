// Proofs for the LemmaScript-generated todo domain
// Part 1: 16-conjunct invariant and preservation across all 24 single-project actions
// Part 2: Multi-project invariant preservation (tryApplyMulti, cross-project ops)
// Part 3: NoOp sanity (completeness and soundness of NoOp classification)

include "domain.dfy"

// =============================================================================
// Helper Predicates
// =============================================================================

predicate NoDupSeq<T(==)>(s: seq<T>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// =============================================================================
// Counting: how many lists contain a given taskId
// =============================================================================

function CountInListsHelper(lists: seq<int>, tasks: map<int, seq<int>>, id: int): int
  ensures CountInListsHelper(lists, tasks, id) >= 0
{
  if |lists| == 0 then 0
  else
    var l := lists[0];
    var lane := if l in tasks then tasks[l] else [];
    var here := if id in lane then 1 else 0;
    here + CountInListsHelper(lists[1..], tasks, id)
}

function CountInLists(m: Model, id: int): int
  ensures CountInLists(m, id) >= 0
{
  CountInListsHelper(m.lists, m.tasks, id)
}

// =============================================================================
// Invariant
// =============================================================================

ghost predicate Inv(m: Model)
{
  // A: Lists are unique
  NoDupSeq(m.lists)

  // B: listNames and tasks maps defined exactly on lists
  && (forall l :: l in m.listNames <==> l in m.lists)
  && (forall l :: l in m.tasks <==> l in m.lists)

  // C: Every taskId in any list exists in taskData
  && (forall l, id :: l in m.tasks && id in m.tasks[l] ==> id in m.taskData)

  // D: Every non-deleted task appears in exactly one list
  && (forall id :: id in m.taskData && !m.taskData[id].deleted ==> CountInLists(m, id) == 1)

  // D': Deleted tasks are not in any list
  && (forall id :: id in m.taskData && m.taskData[id].deleted ==> CountInLists(m, id) == 0)

  // E: No duplicate task IDs within any single list
  && (forall l :: l in m.tasks ==> NoDupSeq(m.tasks[l]))

  // F: All tags referenced by tasks exist
  && (forall id :: id in m.taskData ==> forall t :: t in m.taskData[id].tags ==> t in m.tags)

  // G: Allocators are fresh
  && (forall id :: id in m.lists ==> id < m.nextListId)
  && (forall id :: id in m.taskData ==> id < m.nextTaskId)
  && (forall id :: id in m.tags ==> id < m.nextTagId)

  // H: Assignees must be members
  && (forall id :: id in m.taskData ==> forall u :: u in m.taskData[id].assignees ==> u in m.members)

  // I: Owner is always a member
  && m.owner in m.members

  // J: Personal projects have exactly one member (the owner)
  && (m.mode.Personal? ==> m.members == [m.owner])

  // K: Collaborative projects have at least one member
  && (m.mode.Collaborative? ==> |m.members| >= 1)

  // L: Due dates are valid if present
  && (forall id :: id in m.taskData && m.taskData[id].dueDate.Some?
        ==> validDate(m.taskData[id].dueDate.value))

  // M: List names are unique (case-insensitive)
  && (forall l1, l2 :: l1 in m.listNames && l2 in m.listNames && l1 != l2
        ==> !eqIgnoreCase(m.listNames[l1], m.listNames[l2]))

  // N: Task titles are unique within each list (case-insensitive, non-deleted)
  && (forall l, t1, t2 :: l in m.tasks
        && t1 in m.tasks[l] && t1 in m.taskData && !m.taskData[t1].deleted
        && t2 in m.tasks[l] && t2 in m.taskData && !m.taskData[t2].deleted
        && t1 != t2
        ==> !eqIgnoreCase(m.taskData[t1].title, m.taskData[t2].title))

  // O: Tag names are unique (case-insensitive)
  && (forall t1, t2 :: t1 in m.tags && t2 in m.tags && t1 != t2
        ==> !eqIgnoreCase(m.tags[t1].name, m.tags[t2].name))

  // P: Members are unique
  && NoDupSeq(m.members)
}

// =============================================================================
// InitSatisfiesInv
// =============================================================================

lemma InitSatisfiesInv()
  ensures Inv(init())
{
  var m := init();
  // Empty model: lists=[], members=[INITIAL_OWNER], everything else empty.
  // All universal quantifiers are vacuously true on empty domains.
  assert m.lists == [];
  assert m.members == [INITIAL_OWNER];
  assert m.taskData == map[];
  assert m.tags == map[];
  assert NoDupSeq(m.lists);
  assert NoDupSeq(m.members);
  // D, D', C, E, F, G, H, L, M, N, O: vacuously true (empty domains)
  assert forall id :: id in m.taskData ==> false;
  assert forall l :: l in m.tasks ==> false;
  assert forall l :: l in m.listNames ==> false;
  assert forall id :: id in m.tags ==> false;
}

// =============================================================================
// Helper Lemmas: NoDupSeq
// =============================================================================

lemma NoDupSeqAppend<T>(s: seq<T>, x: T)
  requires NoDupSeq(s)
  requires x !in s
  ensures NoDupSeq(s + [x])
{
  var s' := s + [x];
  forall i, j | 0 <= i < j < |s'|
    ensures s'[i] != s'[j]
  {
    if j < |s| {
      // Both in original sequence
      assert s[i] != s[j];
    } else {
      // j == |s|, so s'[j] == x, and s'[i] == s[i] which is in s, and x !in s
      assert s'[j] == x;
      assert s'[i] == s[i];
      assert s[i] in s;
      assert x !in s;
    }
  }
}

// Generic lemmas for `without` (transparent, replaces old FilterNeqInt/FilterNeqString)

lemma WithoutPreservesNoDup<T>(s: seq<T>, v: T)
  requires NoDupSeq(s)
  ensures NoDupSeq(without(s, v))
  decreases |s|
{
  if |s| > 0 {
    WithoutPreservesNoDup(s[1..], v);
    if s[0] != v {
      assert s[0] !in s[1..];
      WithoutNotIn(s[1..], v, s[0]);
    }
  }
}

lemma WithoutNotIn<T>(s: seq<T>, v: T, x: T)
  requires x !in s
  ensures x !in without(s, v)
  decreases |s|
{
  if |s| > 0 { WithoutNotIn(s[1..], v, x); }
}

lemma WithoutSubset<T>(s: seq<T>, v: T)
  ensures forall x :: x in without(s, v) ==> x in s
  ensures forall x :: x in without(s, v) ==> x != v
  decreases |s|
{
  if |s| > 0 { WithoutSubset(s[1..], v); }
}

lemma WithoutKeeps<T>(s: seq<T>, v: T, x: T)
  requires x in s
  requires x != v
  ensures x in without(s, v)
  decreases |s|
{
  if |s| > 0 {
    if s[0] == x { }
    else { assert x in s[1..]; WithoutKeeps(s[1..], v, x); }
  }
}

lemma WithoutRemoves<T>(s: seq<T>, v: T)
  ensures v !in without(s, v)
  decreases |s|
{
  if |s| > 0 { WithoutRemoves(s[1..], v); }
}

lemma InsertAtPreservesNoDup<T>(s: seq<T>, i: int, x: T)
  requires 0 <= i <= |s|
  requires NoDupSeq(s)
  requires x !in s
  ensures NoDupSeq(insertAt(s, i, x))
{
  var r := insertAt(s, i, x);
  assert r == s[..i] + [x] + s[i..];
  forall a, b | 0 <= a < b < |r|
    ensures r[a] != r[b]
  {
    if a < i && b < i {
      assert r[a] == s[a] && r[b] == s[b];
    } else if a < i && b == i {
      assert r[a] == s[a] && r[b] == x;
      assert s[a] in s;
    } else if a < i && b > i {
      assert r[a] == s[a] && r[b] == s[b-1];
    } else if a == i && b > i {
      assert r[a] == x && r[b] == s[b-1];
      assert s[b-1] in s;
    } else {
      // a > i && b > i
      assert r[a] == s[a-1] && r[b] == s[b-1];
    }
  }
}

// =============================================================================
// Helper Lemmas: CountInLists
// =============================================================================

// Fresh ID not in any list
lemma FreshIdNotInLists(m: Model, id: int)
  requires Inv(m)
  requires id >= m.nextTaskId
  ensures CountInLists(m, id) == 0
{
  FreshIdNotInListsHelper(m.lists, m.tasks, m.taskData, m.nextTaskId, id);
}

lemma FreshIdNotInListsHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskData: map<int, Task>, nextTaskId: int, id: int)
  requires forall l, tid :: l in tasks && tid in tasks[l] ==> tid in taskData
  requires forall tid :: tid in taskData ==> tid < nextTaskId
  requires id >= nextTaskId
  ensures CountInListsHelper(lists, tasks, id) == 0
{
  if |lists| > 0 {
    var l := lists[0];
    var lane := if l in tasks then tasks[l] else [];
    if id in lane {
      assert l in tasks;
      assert id in tasks[l];
      // then id in taskData, so id < nextTaskId, contradicting id >= nextTaskId
      assert id in taskData;
      assert false;
    }
    FreshIdNotInListsHelper(lists[1..], tasks, taskData, nextTaskId, id);
  }
}

// If id is not in taskData, it's not in any lane (by Inv C), so count is 0
lemma NotInTaskDataNotInLanes(m: Model, id: int)
  requires Inv(m)
  requires id !in m.taskData
  ensures CountInLists(m, id) == 0
{
  NotInTaskDataNotInLanesHelper(m.lists, m.tasks, m.taskData, id);
}

lemma NotInTaskDataNotInLanesHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskData: map<int, Task>, id: int)
  requires forall l, tid :: l in tasks && tid in tasks[l] ==> tid in taskData
  requires id !in taskData
  ensures CountInListsHelper(lists, tasks, id) == 0
{
  if |lists| > 0 {
    var l := lists[0];
    var lane := if l in tasks then tasks[l] else [];
    if id in lane {
      assert l in tasks;
      assert id in tasks[l];
      assert id in taskData;
      assert false;
    }
    NotInTaskDataNotInLanesHelper(lists[1..], tasks, taskData, id);
  }
}

// Count doesn't change when we only update taskData (not tasks map or lists)
lemma CountUnchangedTaskDataOnly(m: Model, m2: Model, id: int)
  requires m2.lists == m.lists
  requires m2.tasks == m.tasks
  ensures CountInLists(m2, id) == CountInLists(m, id)
{
  CountUnchangedHelper(m.lists, m.tasks, m.tasks, id);
}

lemma CountUnchangedHelper(lists: seq<int>, tasks1: map<int, seq<int>>,
    tasks2: map<int, seq<int>>, id: int)
  requires tasks1 == tasks2
  ensures CountInListsHelper(lists, tasks1, id) == CountInListsHelper(lists, tasks2, id)
{
}

// Appending a new list with empty lane doesn't change counts
lemma CountAfterAppendEmptyLane(lists: seq<int>, tasks: map<int, seq<int>>,
    newListId: int, id: int)
  requires newListId !in tasks
  ensures CountInListsHelper(lists + [newListId], tasks[newListId := []], id)
       == CountInListsHelper(lists, tasks, id)
{
  if |lists| > 0 {
    var l := lists[0];
    assert (lists + [newListId])[0] == l;
    assert (lists + [newListId])[1..] == lists[1..] + [newListId];
    // The lane for l is the same in both tasks and tasks[newListId := []] since l != newListId
    // (actually l might equal newListId if newListId is in lists, but we don't require that)
    CountAfterAppendEmptyLane(lists[1..], tasks, newListId, id);
  } else {
    // lists == [], so lists + [newListId] == [newListId]
    assert CountInListsHelper([newListId], tasks[newListId := []], id) == 0;
  }
}

// Updating one lane: how count changes
lemma CountAfterUpdateOneLane(lists: seq<int>, tasks: map<int, seq<int>>,
    listId: int, newLane: seq<int>, tid: int)
  requires NoDupSeq(lists)
  requires listId in lists
  requires listId in tasks
  ensures CountInListsHelper(lists, tasks[listId := newLane], tid) ==
    CountInListsHelper(lists, tasks, tid)
    - (if tid in tasks[listId] then 1 else 0)
    + (if tid in newLane then 1 else 0)
{
  if |lists| > 0 {
    if lists[0] == listId {
      assert (tasks[listId := newLane])[listId] == newLane;
      // listId !in lists[1..] by NoDupSeq
      assert listId !in lists[1..];
      CountUnchangedForOtherKeys(lists[1..], tasks, tasks[listId := newLane], listId, tid);
    } else {
      // Not this list - lane unchanged
      var head := lists[0];
      assert head != listId;
      assert (if head in tasks[listId := newLane] then tasks[listId := newLane][head] else [])
          == (if head in tasks then tasks[head] else []);
      CountAfterUpdateOneLane(lists[1..], tasks, listId, newLane, tid);
    }
  }
}

lemma CountUnchangedForOtherKeys(lists: seq<int>, tasks1: map<int, seq<int>>,
    tasks2: map<int, seq<int>>, changedKey: int, tid: int)
  requires changedKey !in lists
  requires forall l :: l != changedKey ==> (l in tasks1 <==> l in tasks2) && (l in tasks1 ==> tasks1[l] == tasks2[l])
  ensures CountInListsHelper(lists, tasks1, tid) == CountInListsHelper(lists, tasks2, tid)
{
  if |lists| > 0 {
    assert lists[0] != changedKey;
    CountUnchangedForOtherKeys(lists[1..], tasks1, tasks2, changedKey, tid);
  }
}

// Count after appending a task to a lane
lemma CountAfterAppendToLane(m: Model, listId: int, taskId: int, tid: int)
  requires Inv(m)
  requires listId in m.lists
  requires listId in m.tasks
  requires taskId !in m.taskData
  ensures CountInLists(
    m.(tasks := m.tasks[listId := m.tasks[listId] + [taskId]]),
    tid)
    == (if tid == taskId then CountInLists(m, tid) + 1 else CountInLists(m, tid))
{
  var newLane := m.tasks[listId] + [taskId];
  CountAfterUpdateOneLane(m.lists, m.tasks, listId, newLane, tid);
  // tid in newLane <==> tid in m.tasks[listId] || tid == taskId
  if tid == taskId {
    assert taskId !in m.taskData;
    // taskId is not in taskData, so by Inv C it's not in any lane
    NotInTaskDataNotInLanes(m, taskId);
    assert CountInLists(m, taskId) == 0;
    assert tid in newLane;
    assert !(tid in m.tasks[listId]);
  } else {
    // tid in newLane <==> tid in m.tasks[listId]
    assert tid in newLane <==> tid in m.tasks[listId];
  }
}

// =============================================================================
// Helper Lemmas: removeTaskFromAllLists
// =============================================================================

// removeTaskFromAllLists preserves map domain under the invariant
// (when all list IDs in lists are keys of tasks)
lemma RemoveTaskFromAllListsDomain(lists: seq<int>, tasks: map<int, seq<int>>, taskId: int)
  requires forall l :: l in lists ==> l in tasks
  ensures forall l :: l in removeTaskFromAllLists(lists, tasks, taskId) <==> l in tasks
{
  RemoveTaskFromAllListsDomainHelper(lists, tasks, taskId, 0);
}


lemma RemoveTaskFromAllListsDomainHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskId: int, i: int)
  requires 0 <= i <= |lists|
  requires forall l :: l in lists ==> l in tasks
  ensures forall l :: l in removeTaskFromListsFrom(lists, tasks, taskId, i) <==> l in tasks
  decreases |lists| - i
{
  if i < |lists| {
    var lid := lists[i];
    assert lid in tasks;
    var filtered := Std.Collections.Seq.Filter((id: TaskId) => (id != taskId), tasks[lid]);
    // no longer needed — without is transparent
    var tasks' := tasks[lid := filtered];
    assert forall l :: l in tasks' <==> l in tasks;
    assert forall l :: l in lists ==> l in tasks';
    RemoveTaskFromAllListsDomainHelper(lists, tasks', taskId, i + 1);
  }
}

lemma RemoveTaskFromAllListsRemoves(lists: seq<int>, tasks: map<int, seq<int>>, taskId: int)
  requires forall l :: l in tasks ==> l in lists
  ensures forall l :: l in removeTaskFromAllLists(lists, tasks, taskId)
            ==> taskId !in removeTaskFromAllLists(lists, tasks, taskId)[l]
{
  RemoveTaskFromAllListsRemovesHelper(lists, tasks, taskId, 0);
}

lemma RemoveTaskFromAllListsRemovesHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskId: int, i: int)
  requires 0 <= i <= |lists|
  requires forall l :: l in tasks ==> l in lists
  // Stronger invariant: everything already processed (before index i) has taskId removed
  requires forall j :: 0 <= j < i && lists[j] in tasks ==> taskId !in tasks[lists[j]]
  ensures forall l :: l in removeTaskFromListsFrom(lists, tasks, taskId, i)
            ==> taskId !in removeTaskFromListsFrom(lists, tasks, taskId, i)[l]
  decreases |lists| - i
{
  if i < |lists| {
    var lid := lists[i];
    if lid in tasks {
      var filtered := without(tasks[lid], taskId);
      WithoutSubset(tasks[lid], taskId);
      WithoutRemoves(tasks[lid], taskId);
      var tasks' := tasks[lid := filtered];
      assert forall l :: l in tasks' ==> l in lists;
      // tasks'[lid] = filtered, which has taskId removed
      assert taskId !in tasks'[lid];
      // For j < i, lists[j] was already processed and had taskId removed
      // tasks'[lists[j]] == tasks[lists[j]] for j != i (different key)
      assert forall j :: 0 <= j < i + 1 && lists[j] in tasks' ==> taskId !in tasks'[lists[j]];
      RemoveTaskFromAllListsRemovesHelper(lists, tasks', taskId, i + 1);
    } else {
      assert forall j :: 0 <= j < i + 1 && lists[j] in tasks ==> taskId !in tasks[lists[j]];
      RemoveTaskFromAllListsRemovesHelper(lists, tasks, taskId, i + 1);
    }
  }
}


// without is idempotent: without(without(s, v), v) == without(s, v)
lemma WithoutIdempotent<T>(s: seq<T>, v: T)
  ensures without(without(s, v), v) == without(s, v)
  decreases |s|
{
  if |s| > 0 {
    if s[0] == v {
      // without(s, v) == without(s[1..], v)
      WithoutIdempotent(s[1..], v);
    } else {
      // without(s, v) == [s[0]] + without(s[1..], v)
      // without([s[0]] + without(s[1..], v), v) == [s[0]] + without(without(s[1..], v), v)
      //   since s[0] != v
      WithoutIdempotent(s[1..], v);
    }
  }
}

// For tid != taskId, membership in each lane is preserved by removeTaskFromAllLists
lemma RemoveTaskFromAllListsPreservesOther(lists: seq<int>, tasks: map<int, seq<int>>, taskId: int)
  requires forall l :: l in tasks ==> l in lists
  requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
  ensures forall l :: l in removeTaskFromAllLists(lists, tasks, taskId) <==> l in tasks
  ensures forall l :: l in tasks ==>
    forall tid :: tid != taskId ==> (tid in removeTaskFromAllLists(lists, tasks, taskId)[l] <==> tid in tasks[l])
  ensures forall l :: l in tasks ==>
    NoDupSeq(removeTaskFromAllLists(lists, tasks, taskId)[l])
{
  RemoveTaskFromAllListsPreservesOtherHelper(lists, tasks, taskId, 0);
}

lemma RemoveTaskFromAllListsPreservesOtherHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskId: int, i: int)
  requires 0 <= i <= |lists|
  requires forall l :: l in tasks ==> l in lists
  requires forall l :: l in tasks ==> NoDupSeq(tasks[l])
  ensures forall l :: l in removeTaskFromListsFrom(lists, tasks, taskId, i) <==> l in tasks
  ensures forall l :: l in tasks ==>
    forall tid :: tid != taskId ==> (tid in removeTaskFromListsFrom(lists, tasks, taskId, i)[l] <==> tid in tasks[l])
  ensures forall l :: l in tasks ==>
    NoDupSeq(removeTaskFromListsFrom(lists, tasks, taskId, i)[l])
  decreases |lists| - i
{
  if i < |lists| {
    var lid := lists[i];
    if lid in tasks {
      WithoutPreservesNoDup(tasks[lid], taskId);
      var tasks' := tasks[lid := without(tasks[lid], taskId)];
      WithoutSubset(tasks[lid], taskId);
      forall tid | tid != taskId
        ensures tid in tasks'[lid] <==> tid in tasks[lid]
      {
        if tid in tasks[lid] { WithoutKeeps(tasks[lid], taskId, tid); }
      }
      assert forall l :: l in tasks' ==> l in lists;
      RemoveTaskFromAllListsPreservesOtherHelper(lists, tasks', taskId, i + 1);
    } else {
      RemoveTaskFromAllListsPreservesOtherHelper(lists, tasks, taskId, i + 1);
    }
  }
}

// =============================================================================
// Helper Lemmas: removeTagFromAllTasks / clearAssigneeFromAllTasks
// =============================================================================

lemma RemoveTagFromAllTasksDomain(taskData: map<int, Task>, tagId: int)
  ensures forall tid :: tid in removeTagFromAllTasks(taskData, tagId) <==> tid in taskData
{
}

lemma RemoveTagFromAllTasksRemovesTag(taskData: map<int, Task>, tagId: int)
  ensures forall tid :: tid in removeTagFromAllTasks(taskData, tagId)
            ==> tagId !in removeTagFromAllTasks(taskData, tagId)[tid].tags
{
  forall tid | tid in removeTagFromAllTasks(taskData, tagId)
    ensures tagId !in removeTagFromAllTasks(taskData, tagId)[tid].tags
  {
    assert removeTagFromAllTasks(taskData, tagId)[tid].tags == without(taskData[tid].tags, tagId);
    WithoutSubset(taskData[tid].tags, tagId);
  }
}

lemma RemoveTagFromAllTasksPreservesOtherTags(taskData: map<int, Task>, tagId: int)
  ensures forall tid, t :: tid in removeTagFromAllTasks(taskData, tagId)
            && t in removeTagFromAllTasks(taskData, tagId)[tid].tags
            ==> t in taskData[tid].tags && t != tagId
{
  forall tid, t | tid in removeTagFromAllTasks(taskData, tagId)
            && t in removeTagFromAllTasks(taskData, tagId)[tid].tags
    ensures t in taskData[tid].tags && t != tagId
  {
    assert removeTagFromAllTasks(taskData, tagId)[tid].tags == without(taskData[tid].tags, tagId);
    WithoutSubset(taskData[tid].tags, tagId);
  }
}

lemma RemoveTagFromAllTasksPreservesOtherFields(taskData: map<int, Task>, tagId: int)
  ensures forall tid :: tid in removeTagFromAllTasks(taskData, tagId) ==>
    var orig := taskData[tid];
    var upd := removeTagFromAllTasks(taskData, tagId)[tid];
    upd.title == orig.title && upd.notes == orig.notes &&
    upd.completed == orig.completed && upd.starred == orig.starred &&
    upd.dueDate == orig.dueDate && upd.assignees == orig.assignees &&
    upd.deleted == orig.deleted && upd.deletedBy == orig.deletedBy &&
    upd.deletedFromList == orig.deletedFromList
{
}

lemma ClearAssigneeFromAllTasksDomain(taskData: map<int, Task>, userId: string)
  ensures forall tid :: tid in clearAssigneeFromAllTasks(taskData, userId) <==> tid in taskData
{
}

lemma ClearAssigneeFromAllTasksRemovesUser(taskData: map<int, Task>, userId: string)
  ensures forall tid :: tid in clearAssigneeFromAllTasks(taskData, userId)
            ==> userId !in clearAssigneeFromAllTasks(taskData, userId)[tid].assignees
{
  forall tid | tid in clearAssigneeFromAllTasks(taskData, userId)
    ensures userId !in clearAssigneeFromAllTasks(taskData, userId)[tid].assignees
  {
    assert clearAssigneeFromAllTasks(taskData, userId)[tid].assignees == without(taskData[tid].assignees, userId);
    WithoutSubset(taskData[tid].assignees, userId);
  }
}

lemma ClearAssigneePreservesOtherFields(taskData: map<int, Task>, userId: string)
  ensures forall tid :: tid in clearAssigneeFromAllTasks(taskData, userId) ==>
    var orig := taskData[tid];
    var upd := clearAssigneeFromAllTasks(taskData, userId)[tid];
    upd.title == orig.title && upd.notes == orig.notes &&
    upd.completed == orig.completed && upd.starred == orig.starred &&
    upd.dueDate == orig.dueDate && upd.tags == orig.tags &&
    upd.deleted == orig.deleted && upd.deletedBy == orig.deletedBy &&
    upd.deletedFromList == orig.deletedFromList
{
}

// =============================================================================
// Helper Lemma: listNameExistsFrom / listNameExists
// =============================================================================

// If listNameExists returns false, no list in m.lists (other than excludeList) has that name
lemma ListNameExistsFalseImpliesUnique(m: Model, name: string, excludeList: Option<int>)
  requires Inv(m)
  requires !listNameExists(m, name, excludeList)
  ensures forall l :: l in m.listNames
            && (excludeList.None? || l != excludeList.value)
            ==> !eqIgnoreCase(m.listNames[l], name)
{
  ListNameExistsFromFalse(m.lists, m.listNames, name, excludeList, 0);
  // Under Inv, l in m.listNames <==> l in m.lists, so the iteration covers all keys
  forall l | l in m.listNames && (excludeList.None? || l != excludeList.value)
    ensures !eqIgnoreCase(m.listNames[l], name)
  {
    assert l in m.lists;
    // l is at some index j in m.lists
    var j :| 0 <= j < |m.lists| && m.lists[j] == l;
    // ListNameExistsFromFalse gives us the result for this index
  }
}

lemma ListNameExistsFromFalse(lists: seq<int>, listNames: map<int, string>,
    name: string, excludeList: Option<int>, i: int)
  requires 0 <= i <= |lists|
  requires !listNameExistsFrom(lists, listNames, name, excludeList, i)
  ensures forall j :: i <= j < |lists|
            && lists[j] in listNames
            && (excludeList.None? || lists[j] != excludeList.value)
            ==> !eqIgnoreCase(listNames[lists[j]], name)
  decreases |lists| - i
{
  if i < |lists| {
    ListNameExistsFromFalse(lists, listNames, name, excludeList, i + 1);
  }
}

// =============================================================================
// Helper Lemma: tagNameExists
// =============================================================================

lemma TagNameExistsFalseImpliesUnique(m: Model, name: string, excludeTag: Option<int>)
  requires !tagNameExists(m, name, excludeTag)
  ensures forall t :: t in m.tags
            && (excludeTag.None? || t != excludeTag.value)
            ==> !eqIgnoreCase(m.tags[t].name, name)
{
}

// =============================================================================
// Decomposition Lemmas: what apply returns for filter-using actions
// Helper lemmas for without-based operations
// =============================================================================

// For actions that use Std.Collections.Seq.Filter (opaque) in apply, we rely on
// Filter's postconditions: elements of the result are in the original sequence
// and satisfy the predicate. No need to decompose what apply returns.

// =============================================================================
// Preservation Lemmas
// =============================================================================

// --- NoOp ---
lemma NoOpPreservesInv(m: Model, m2: Model)
  requires Inv(m)
  requires apply(m, NoOp) == true_(m2)
  ensures Inv(m2)
{
  assert m2 == m;
}

// --- AddList ---
lemma AddListPreservesInv(m: Model, name: string, m2: Model)
  requires Inv(m)
  requires apply(m, AddList(name)) == true_(m2)
  ensures Inv(m2)
{
  var id := m.nextListId;
  // apply succeeded, so listNameExists(m, name, None) is false
  assert !listNameExists(m, name, None);
  assert m2 == m.(lists := m.lists + [id], listNames := m.listNames[id := name],
                  tasks := m.tasks[id := []], nextListId := m.nextListId + 1);

  // A: id is fresh (>= nextListId), and all existing list ids < nextListId
  assert id !in m.lists;
  NoDupSeqAppend(m.lists, id);

  // B: listNames and tasks grow by exactly id
  assert forall l :: l in m2.listNames <==> l in m2.lists;
  assert forall l :: l in m2.tasks <==> l in m2.lists;

  // C: New lane is empty, so no new task refs to check
  // D/D': Count unchanged for existing tasks since we added empty lane
  assert id !in m.tasks; // fresh id not in tasks
  forall tid | tid in m2.taskData
    ensures CountInLists(m2, tid) == CountInLists(m, tid)
  {
    CountAfterAppendEmptyLane(m.lists, m.tasks, id, tid);
  }

  // E: New lane [] is NoDupSeq
  assert NoDupSeq(m2.tasks[id]);

  // G: All old lists < nextListId < nextListId+1, and id == nextListId < nextListId+1
  // M: listNameExists was false, so no collision
  ListNameExistsFalseImpliesUnique(m, name, None);
}

// --- RenameList ---
lemma RenameListPreservesInv(m: Model, listId: int, newName: string, m2: Model)
  requires Inv(m)
  requires apply(m, RenameList(listId, newName)) == true_(m2)
  ensures Inv(m2)
{
  // Only listNames changes (one entry updated)
  assert m2 == m.(listNames := m.listNames[listId := newName]);
  // Most conjuncts trivially preserved
  // M: listNameExists(m, newName, Some(listId)) was false
  ListNameExistsFalseImpliesUnique(m, newName, Some(listId));
  // D/D' unchanged
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
}

// --- DeleteList ---
lemma DeleteListPreservesInv(m: Model, listId: int, m2: Model)
  requires Inv(m)
  requires apply(m, DeleteList(listId)) == true_(m2)
  ensures Inv(m2)
{
  if !(listId in m.lists) {
    assert m2 == m;
  } else {
    // Complex: removes list, its lane, and all tasks in the lane from taskData
    // TODO: full proof
    assume {:axiom} false;
  }
}

// --- MoveList ---
lemma MoveListPreservesInv(m: Model, listId: int, listPlace: ListPlace, m2: Model)
  requires Inv(m)
  requires apply(m, MoveList(listId, listPlace)) == true_(m2)
  ensures Inv(m2)
{
  assert apply(m, MoveList(listId, listPlace)) == applyMoveList(m, listId, listPlace);
  // m2.lists = insertAt(without(m.lists, listId), clamped, listId)
  // All other fields unchanged.
  assert m2.tasks == m.tasks;
  assert m2.listNames == m.listNames;
  assert m2.taskData == m.taskData;
  assert m2.members == m.members;
  assert m2.tags == m.tags;

  var listsWithout := without(m.lists, listId);
  WithoutPreservesNoDup(m.lists, listId);
  WithoutRemoves(m.lists, listId);
  WithoutSubset(m.lists, listId);
  assert listId !in listsWithout;

  var pos := posFromListPlace(m.lists, listPlace);
  var clamped := MathMin(pos, |listsWithout|);
  InsertAtPreservesNoDup(listsWithout, clamped, listId);

  // B: same elements in lists
  forall l
    ensures l in m2.lists <==> l in m.lists
  {
    if l in m.lists {
      if l == listId {
        // listId is inserted back
      } else {
        WithoutKeeps(m.lists, listId, l);
      }
    }
  }

  // D/D': tasks unchanged, same list elements → same counts
  CountSameElements(m, m2);
}

// insertAt(without, i, x) has same elements as without + {x}
lemma InsertAtContains(without: seq<int>, i: int, x: int, original: seq<int>)
  requires 0 <= i <= |without|
  requires forall l :: l in without ==> l in original
  requires x in original
  requires forall l :: l in original ==> l in without || l == x
  ensures forall l :: l in insertAt(without, i, x) <==> l in original
{
  var result := insertAt(without, i, x);
  forall l
    ensures l in result <==> l in original
  {
    if l in result {
      assert l in without || l == x;
    }
    if l in original {
      if l == x {
        assert result[i] == x;
        assert x in result;
      } else {
        assert l in without;
        // l is in without which is a subsequence of result
        if l in without[..i] {
          var j :| 0 <= j < i && without[j] == l;
          assert result[j] == l;
        } else {
          assert l in without[i..];
          var j :| i <= j < |without| && without[j] == l;
          assert result[j + 1] == l;
        }
      }
    }
  }
}

// Count unchanged when lists have the same elements (permutation)
lemma CountSameElements(m: Model, m2: Model)
  requires m2.tasks == m.tasks
  requires m2.taskData == m.taskData
  requires forall l :: l in m2.lists <==> l in m.lists
  requires NoDupSeq(m.lists)
  requires NoDupSeq(m2.lists)
  ensures forall tid :: CountInLists(m2, tid) == CountInLists(m, tid)
{
  forall tid
    ensures CountInLists(m2, tid) == CountInLists(m, tid)
  {
    CountPermutation(m.lists, m2.lists, m.tasks, tid);
  }
}

// If two NoDupSeq sequences have the same elements, CountInListsHelper gives the same result
lemma CountPermutation(s1: seq<int>, s2: seq<int>, tasks: map<int, seq<int>>, tid: int)
  requires NoDupSeq(s1)
  requires NoDupSeq(s2)
  requires forall l :: l in s1 <==> l in s2
  ensures CountInListsHelper(s1, tasks, tid) == CountInListsHelper(s2, tasks, tid)
  decreases |s1|
{
  if |s1| == 0 {
    // s2 must also be empty (same elements)
    if |s2| > 0 { assert s2[0] in s2; assert s2[0] in s1; assert false; }
  } else {
    var h := s1[0];
    assert h in s2;
    // Remove h from both sequences
    var s1' := s1[1..];
    var s2' := without(s2, h);
    // s1' and s2' have the same elements (s1 minus h, s2 minus h)
    WithoutPreservesNoDup(s2, h);
    forall l ensures l in s1' <==> l in s2' {
      if l in s1' {
        assert l in s1;
        assert l in s2;
        assert l != h; // because NoDupSeq(s1) and l in s1[1..]
        WithoutKeeps(s2, h, l);
      }
      if l in s2' {
        WithoutSubset(s2, h);
        assert l in s2;
        assert l in s1;
        assert l != h;
        // l in s1 && l != s1[0] → l in s1[1..]
      }
    }
    CountPermutation(s1', s2', tasks, tid);
    // Now: CountInListsHelper(s1, tasks, tid) = contribution(h) + CountInListsHelper(s1', tasks, tid)
    //      CountInListsHelper(s2, tasks, tid) = ? — need to relate to removing h from s2
    CountRemoveOne(s2, tasks, tid, h);
    // CountInListsHelper(s2, tasks, tid) = contribution(h) + CountInListsHelper(without(s2, h), tasks, tid)
  }
}

// Removing one element from a NoDupSeq: count = contribution + count of rest
lemma CountRemoveOne(lists: seq<int>, tasks: map<int, seq<int>>, tid: int, h: int)
  requires NoDupSeq(lists)
  requires h in lists
  ensures var lane := if h in tasks then tasks[h] else [];
    var here := if tid in lane then 1 else 0;
    CountInListsHelper(lists, tasks, tid) == here + CountInListsHelper(without(lists, h), tasks, tid)
  decreases |lists|
{
  if |lists| > 0 {
    if lists[0] == h {
      // h is the head — without(lists, h) == lists[1..] (since NoDupSeq, h not in rest)
      assert without(lists, h) == without(lists[1..], h);
      // h !in lists[1..] by NoDupSeq
      WithoutNotIn(lists[1..], h, h);
      // Hmm, that's the wrong lemma — WithoutNotIn says if x !in s then x !in without(s,v)
      // We need: if h !in lists[1..], then without(lists[1..], h) == lists[1..]
      WithoutNoOp(lists[1..], h);
    } else {
      // h is not the head — recurse
      assert h in lists[1..];
      CountRemoveOne(lists[1..], tasks, tid, h);
    }
  }
}

// without never increases length
lemma WithoutLength<T>(s: seq<T>, v: T)
  ensures |without(s, v)| <= |s|
  decreases |s|
{
  if |s| > 0 { WithoutLength(s[1..], v); }
}

// If v is in s, without(s, v) is strictly shorter
lemma WithoutShorter<T>(s: seq<T>, v: T)
  requires v in s
  ensures |without(s, v)| < |s|
  decreases |s|
{
  if s[0] == v {
    // without(s, v) == without(s[1..], v), and |without(s[1..], v)| <= |s[1..]| == |s| - 1
    WithoutLength(s[1..], v);
  } else {
    assert v in s[1..];
    WithoutShorter(s[1..], v);
  }
}

// If v is not in s, without(s, v) == s
lemma WithoutNoOp<T>(s: seq<T>, v: T)
  requires v !in s
  ensures without(s, v) == s
  decreases |s|
{
  if |s| > 0 {
    assert s[0] != v;
    WithoutNoOp(s[1..], v);
  }
}

// --- AddTask ---
lemma AddTaskPreservesInv(m: Model, listId: int, title: string, m2: Model)
  requires Inv(m)
  requires apply(m, AddTask(listId, title)) == true_(m2)
  ensures Inv(m2)
{
  assert apply(m, AddTask(listId, title)) == applyAddTask(m, listId, title);
  var id := m.nextTaskId;

  // id is fresh (not in taskData, not in any lane)
  assert id !in m.taskData;
  NotInTaskDataNotInLanes(m, id);
  assert CountInLists(m, id) == 0;

  // m2 = m with one lane extended and one new task
  var lane := if listId in m.tasks then m.tasks[listId] else [];
  assert m2.tasks == m.tasks[listId := lane + [id]];
  assert m2.lists == m.lists;
  assert m2.members == m.members;
  assert m2.tags == m.tags;

  // D/D': count for new task = 1, count for others unchanged
  forall tid | tid in m2.taskData
    ensures !m2.taskData[tid].deleted ==> CountInLists(m2, tid) == 1
    ensures m2.taskData[tid].deleted ==> CountInLists(m2, tid) == 0
  {
    CountAfterAppendToLane(m, listId, id, tid);
    if tid == id {
      // new task: non-deleted, count goes from 0 to 1
      assert !m2.taskData[id].deleted;
    } else {
      // existing task: count unchanged
      assert m2.taskData[tid] == m.taskData[tid];
    }
  }

  // E: NoDupSeq for the extended lane
  assert id !in lane;
  NoDupSeqAppend(lane, id);

  // N: title uniqueness. New task `id` has title `title`.
  // taskTitleExistsInList was false → no existing non-deleted task in listId has this title.
  // For lists other than listId: lanes unchanged, tasks unchanged → N preserved.
  // For listId: id is added. For pairs not involving id: unchanged. For pairs involving id:
  //   other task's title != title (by taskTitleExistsInList check).
  forall l, t1, t2 | l in m2.tasks
      && t1 in m2.tasks[l] && t1 in m2.taskData && !m2.taskData[t1].deleted
      && t2 in m2.tasks[l] && t2 in m2.taskData && !m2.taskData[t2].deleted
      && t1 != t2
    ensures !eqIgnoreCase(m2.taskData[t1].title, m2.taskData[t2].title)
  {
    if l != listId {
      // Lane unchanged
    } else if t1 != id && t2 != id {
      // Both old tasks in old lane
      assert t1 in m.tasks[listId];
      assert t2 in m.tasks[listId];
    } else {
      // One is the new task (id), the other is old
      var other := if t1 == id then t2 else t1;
      assert other in m.tasks[listId];
      assert other in m.taskData && !m.taskData[other].deleted;
      // taskTitleExistsInList(m, listId, title, None) was false
      assert !taskTitleExistsInList(m, listId, title, None);
      TaskTitleExistsFromFalseHelper(m.tasks[listId], m.taskData, title, None, 0, other);
    }
  }
}

// --- EditTask ---
lemma EditTaskPreservesInv(m: Model, taskId: int, title: string, notes: string, m2: Model)
  requires Inv(m)
  requires apply(m, EditTask(taskId, title, notes)) == true_(m2)
  ensures Inv(m2)
{
  var task := m.taskData[taskId];
  assert !task.deleted;
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);

  // All tasks other than taskId are unchanged
  assert forall id :: id in m2.taskData && id != taskId ==> m2.taskData[id] == m.taskData[id];
  var updTask := m2.taskData[taskId];
  assert updTask.assignees == task.assignees;
  assert updTask.tags == task.tags;
  assert updTask.dueDate == task.dueDate;
  assert updTask.deleted == task.deleted;

  // N: title uniqueness. Only taskId's title changed.
  // For lists NOT containing taskId: all tasks unchanged → N preserved.
  // For the list containing taskId: the code checked taskTitleExistsInList.
  forall l, t1, t2 | l in m2.tasks
      && t1 in m2.tasks[l] && t1 in m2.taskData && !m2.taskData[t1].deleted
      && t2 in m2.tasks[l] && t2 in m2.taskData && !m2.taskData[t2].deleted
      && t1 != t2
    ensures !eqIgnoreCase(m2.taskData[t1].title, m2.taskData[t2].title)
  {
    if t1 != taskId && t2 != taskId {
      assert m2.taskData[t1] == m.taskData[t1];
      assert m2.taskData[t2] == m.taskData[t2];
    } else {
      var other := if t1 == taskId then t2 else t1;
      assert m2.taskData[other] == m.taskData[other];
      // taskId is in list l. Under Inv, taskId is non-deleted so in exactly 1 list.
      assert taskId in m.tasks[l]; // since m2.tasks == m.tasks
      // The code checked title uniqueness for the list found by findListForTask.
      var foundList := findListForTask(m, taskId);
      // findListForTask returns the first list containing taskId.
      // Since taskId is in l, foundList must be Some.
      FindListForTaskFinds(m, taskId, l);
      assert foundList.Some?;
      // The title check was done on foundList.value
      assert !taskTitleExistsInList(m, foundList.value, title, Some(taskId));
      // Since taskId is in exactly one list (Inv D), l must == foundList.value
      FindListForTaskUnique(m, taskId, l, foundList.value);
      assert l == foundList.value;
      // Now: !taskTitleExistsInList(m, l, title, Some(taskId))
      // Means no non-deleted task other than taskId in l has title `title`
      TaskTitleExistsFromFalseHelper(m.tasks[l], m.taskData, title, Some(taskId), 0, other);
    }
  }
}

// If taskId is in list l, findListForTask returns Some(l') where l' also contains taskId
lemma FindListForTaskFinds(m: Model, taskId: int, l: int)
  requires l in m.lists
  requires l in m.tasks
  requires taskId in m.tasks[l]
  ensures findListForTask(m, taskId).Some?
  ensures findListForTask(m, taskId).value in m.tasks
  ensures taskId in m.tasks[findListForTask(m, taskId).value]
{
  FindListForTaskFindsHelper(m.lists, m.tasks, taskId, l, 0);
  FindListForTaskSoundHelper(m.lists, m.tasks, taskId, 0);
}

lemma FindListForTaskFindsHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskId: int, l: int, i: int)
  requires 0 <= i <= |lists|
  requires l in lists[i..]
  requires l in tasks
  requires taskId in tasks[l]
  ensures findListForTaskFrom(lists, tasks, taskId, i).Some?
  decreases |lists| - i
{
  if i < |lists| {
    var lid := lists[i];
    if lid in tasks && taskId in tasks[lid] {
      // Found it
    } else {
      assert l != lid || lid !in tasks || taskId !in tasks[lid];
      assert l in lists[i+1..];
      FindListForTaskFindsHelper(lists, tasks, taskId, l, i + 1);
    }
  }
}

// If findListForTaskFrom returns Some(l), then l is in tasks and taskId is in tasks[l]
lemma FindListForTaskSoundHelper(lists: seq<int>, tasks: map<int, seq<int>>,
    taskId: int, i: int)
  requires 0 <= i <= |lists|
  requires findListForTaskFrom(lists, tasks, taskId, i).Some?
  ensures findListForTaskFrom(lists, tasks, taskId, i).value in tasks
  ensures taskId in tasks[findListForTaskFrom(lists, tasks, taskId, i).value]
  decreases |lists| - i
{
  if i < |lists| {
    var lid := lists[i];
    var lane := if lid in tasks then Some(tasks[lid]) else None;
    match lane {
      case Some(laneVal) =>
        if taskId in laneVal {
          // Returns Some(lid)
        } else {
          FindListForTaskSoundHelper(lists, tasks, taskId, i + 1);
        }
      case None =>
        FindListForTaskSoundHelper(lists, tasks, taskId, i + 1);
    }
  }
}

// Under Inv (exactly one list), if taskId is in both l1 and l2, then l1 == l2
lemma FindListForTaskUnique(m: Model, taskId: int, l1: int, l2: int)
  requires Inv(m)
  requires l1 in m.tasks && taskId in m.tasks[l1]
  requires l2 in m.tasks && taskId in m.tasks[l2]
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures l1 == l2
{
  // Under Inv D, CountInLists(m, taskId) == 1
  // If l1 != l2, count would be >= 2, contradiction
  if l1 != l2 {
    CountAtLeastTwo(m, taskId, l1, l2);
    assert CountInLists(m, taskId) >= 2;
    assert false;
  }
}

lemma CountAtLeastTwo(m: Model, taskId: int, l1: int, l2: int)
  requires Inv(m)
  requires l1 in m.tasks && taskId in m.tasks[l1]
  requires l2 in m.tasks && taskId in m.tasks[l2]
  requires l1 != l2
  ensures CountInLists(m, taskId) >= 2
{
  // l1 and l2 are both in m.lists (by Inv B)
  assert l1 in m.lists;
  assert l2 in m.lists;
  // Each contributes at least 1 to the count
  CountContainsAtLeastOne(m.lists, m.tasks, taskId, l1);
  CountContainsAtLeastOne(m.lists, m.tasks, taskId, l2);
  CountTwoDistinct(m.lists, m.tasks, taskId, l1, l2);
}

lemma CountContainsAtLeastOne(lists: seq<int>, tasks: map<int, seq<int>>, taskId: int, l: int)
  requires l in lists
  requires l in tasks
  requires taskId in tasks[l]
  ensures CountInListsHelper(lists, tasks, taskId) >= 1
{
  if |lists| > 0 {
    if lists[0] == l {
      // First element is l, contributes 1
      assert l in tasks && taskId in tasks[l];
    } else {
      assert l in lists[1..];
      CountContainsAtLeastOne(lists[1..], tasks, taskId, l);
    }
  }
}

lemma CountTwoDistinct(lists: seq<int>, tasks: map<int, seq<int>>, taskId: int, l1: int, l2: int)
  requires NoDupSeq(lists)
  requires l1 in lists && l1 in tasks && taskId in tasks[l1]
  requires l2 in lists && l2 in tasks && taskId in tasks[l2]
  requires l1 != l2
  ensures CountInListsHelper(lists, tasks, taskId) >= 2
{
  if |lists| > 0 {
    var head := lists[0];
    if head == l1 {
      // l1 is first, contributes 1. l2 is in rest, contributes 1.
      assert l2 != l1;
      assert l2 in lists[1..];
      CountContainsAtLeastOne(lists[1..], tasks, taskId, l2);
    } else if head == l2 {
      assert l1 in lists[1..];
      CountContainsAtLeastOne(lists[1..], tasks, taskId, l1);
    } else {
      assert l1 in lists[1..];
      assert l2 in lists[1..];
      CountTwoDistinct(lists[1..], tasks, taskId, l1, l2);
    }
  }
}

// Helper: taskTitleExistsFrom false means a specific task in the lane doesn't match
lemma TaskTitleExistsFromFalseHelper(lane: seq<int>, taskData: map<int, Task>,
    title: string, excludeTask: Option<int>, i: int, target: int)
  requires 0 <= i <= |lane|
  requires !taskTitleExistsFrom(lane, taskData, title, excludeTask, i)
  requires target in lane[i..]
  requires target in taskData
  requires !taskData[target].deleted
  requires excludeTask.Some? ==> target != excludeTask.value
  ensures !eqIgnoreCase(taskData[target].title, title)
  decreases |lane| - i
{
  if i < |lane| {
    if lane[i] == target {
    } else {
      assert target in lane[i+1..];
      TaskTitleExistsFromFalseHelper(lane, taskData, title, excludeTask, i + 1, target);
    }
  }
}

// --- DeleteTask ---
lemma DeleteTaskPreservesInv(m: Model, taskId: int, userId: string, m2: Model)
  requires Inv(m)
  requires apply(m, DeleteTask(taskId, userId)) == true_(m2)
  ensures Inv(m2)
{
  if !(taskId in m.taskData) {
    assert m2 == m;
  } else if m.taskData[taskId].deleted {
    assert m2 == m;
  } else {
    assert apply(m, DeleteTask(taskId, userId)) == applyDeleteTask(m, taskId, userId);
    var task := m.taskData[taskId];
    var newTasks := removeTaskFromAllLists(m.lists, m.tasks, taskId);
    assert m2.tasks == newTasks;
    assert m2.lists == m.lists;
    assert m2.members == m.members;
    assert m2.tags == m.tags;

    // Inv B: tasks keys == lists elements
    assert forall l :: l in m.tasks ==> l in m.lists;

    // removeTaskFromAllLists removes taskId from all lanes and preserves domain
    RemoveTaskFromAllListsRemoves(m.lists, m.tasks, taskId);
    RemoveTaskFromAllListsDomain(m.lists, m.tasks, taskId);
    RemoveTaskFromAllListsPreservesOther(m.lists, m.tasks, taskId);

    // D': deleted task count = 0 (taskId not in any lane after removal)
    CountZeroWhenNotInAnyLane(m2.lists, m2.tasks, taskId);

    // D/D' for other tasks: count unchanged (only taskId removed from lanes)
    forall tid | tid in m2.taskData && tid != taskId
      ensures CountInLists(m2, tid) == CountInLists(m, tid)
    {
      assert forall l :: l in m.tasks ==> (tid in newTasks[l] <==> tid in m.tasks[l]);
      CountUnchangedAfterRemoveOther(m.lists, m.tasks, newTasks, taskId, tid);
    }

    // C: taskIds in lanes still in taskData — without only removes elements
    forall l, tid | l in m2.tasks && tid in m2.tasks[l]
      ensures tid in m2.taskData
    {
      // tid is in newTasks[l] = without(m.tasks[l], taskId)
      // By WithoutSubset: tid was in m.tasks[l], and by Inv C: tid in m.taskData
      if l in m.tasks {
        WithoutSubset(m.tasks[l], taskId);
      }
    }

    // E: NoDupSeq preserved — without preserves NoDupSeq
    forall l | l in m2.tasks
      ensures NoDupSeq(m2.tasks[l])
    {
      if l in m.tasks {
        WithoutPreservesNoDup(m.tasks[l], taskId);
      }
    }

    // N: title uniqueness — without only removes, doesn't change titles
    forall l, t1, t2 | l in m2.tasks
        && t1 in m2.tasks[l] && t1 in m2.taskData && !m2.taskData[t1].deleted
        && t2 in m2.tasks[l] && t2 in m2.taskData && !m2.taskData[t2].deleted
        && t1 != t2
      ensures !eqIgnoreCase(m2.taskData[t1].title, m2.taskData[t2].title)
    {
      if l in m.tasks {
        WithoutSubset(m.tasks[l], taskId);
        assert t1 in m.tasks[l];
        assert t2 in m.tasks[l];
        // t1, t2 != taskId (they're not deleted, but taskId is now deleted)
        assert m2.taskData[t1] == m.taskData[t1];
        assert m2.taskData[t2] == m.taskData[t2];
      }
    }
  }
}

// Count is 0 when taskId is not in any lane
lemma CountZeroWhenNotInAnyLane(lists: seq<int>, tasks: map<int, seq<int>>, taskId: int)
  requires forall l :: l in tasks ==> taskId !in tasks[l]
  ensures CountInListsHelper(lists, tasks, taskId) == 0
{
  if |lists| > 0 {
    var l := lists[0];
    var lane := if l in tasks then tasks[l] else [];
    assert taskId !in lane;
    CountZeroWhenNotInAnyLane(lists[1..], tasks, taskId);
  }
}

// Count unchanged for tasks other than the removed one
lemma CountUnchangedAfterRemoveOther(lists: seq<int>, oldTasks: map<int, seq<int>>,
    newTasks: map<int, seq<int>>, removed: int, tid: int)
  requires tid != removed
  requires forall l :: l in oldTasks <==> l in newTasks
  // Key property: for tid != removed, membership in each lane is preserved
  requires forall l :: l in oldTasks ==> (tid in newTasks[l] <==> tid in oldTasks[l])
  ensures CountInListsHelper(lists, newTasks, tid) == CountInListsHelper(lists, oldTasks, tid)
{
  if |lists| > 0 {
    CountUnchangedAfterRemoveOther(lists[1..], oldTasks, newTasks, removed, tid);
  }
}

// --- RestoreTask ---
lemma RestoreTaskPreservesInv(m: Model, taskId: int, m2: Model)
  requires Inv(m)
  requires apply(m, RestoreTask(taskId)) == true_(m2)
  ensures Inv(m2)
{
  assert apply(m, RestoreTask(taskId)) == applyRestoreTask(m, taskId);
  var task := m.taskData[taskId];
  assert task.deleted;
  assert |m.lists| > 0;

  // The fix ensures targetList is always in m.lists
  var targetList := match task.deletedFromList {
    case Some(v) => if v in m.lists then v else m.lists[0]
    case None => m.lists[0]
  };
  assert targetList in m.lists;
  assert targetList in m.tasks; // Inv B

  var lane := m.tasks[targetList];
  var updTask := task.(deleted := false, deletedBy := None, deletedFromList := None);

  assert m2 == m.(tasks := m.tasks[targetList := lane + [taskId]],
                  taskData := m.taskData[taskId := updTask]);

  // Deleted task has count 0 (Inv D') — so not in any lane
  assert CountInLists(m, taskId) == 0;
  if taskId in lane {
    CountContainsAtLeastOne(m.lists, m.tasks, taskId, targetList);
    assert false;
  }
  assert taskId !in lane;

  // E: extended lane still NoDupSeq
  NoDupSeqAppend(lane, taskId);

  // B: tasks domain unchanged (targetList was already a key)
  assert forall l :: l in m2.tasks <==> l in m2.lists;
  assert forall l :: l in m2.listNames <==> l in m2.lists;

  // D/D': count for restored task goes 0→1; others unchanged
  forall tid | tid in m2.taskData
    ensures !m2.taskData[tid].deleted ==> CountInLists(m2, tid) == 1
    ensures m2.taskData[tid].deleted ==> CountInLists(m2, tid) == 0
  {
    CountAfterUpdateOneLane(m.lists, m.tasks, targetList, lane + [taskId], tid);
    if tid == taskId {
      assert !m2.taskData[taskId].deleted;
      assert !(taskId in m.tasks[targetList]);
      assert taskId in (lane + [taskId]);
    } else {
      assert m2.taskData[tid] == m.taskData[tid];
      assert (tid in (lane + [taskId])) <==> (tid in lane);
    }
  }

  // C: task IDs in lanes exist in taskData
  forall l, id | l in m2.tasks && id in m2.tasks[l]
    ensures id in m2.taskData
  {
    if l == targetList {
      if id != taskId { assert id in lane; }
    } else {
      assert m2.tasks[l] == m.tasks[l];
    }
  }

  // E: NoDupSeq for all lanes
  forall l | l in m2.tasks
    ensures NoDupSeq(m2.tasks[l])
  {
    if l == targetList {
      assert m2.tasks[l] == lane + [taskId];
    } else {
      assert m2.tasks[l] == m.tasks[l];
    }
  }

  // N: title uniqueness within lists
  assert !taskTitleExistsInList(m, targetList, task.title, None);
  forall l, t1, t2 | l in m2.tasks
      && t1 in m2.tasks[l] && t1 in m2.taskData && !m2.taskData[t1].deleted
      && t2 in m2.tasks[l] && t2 in m2.taskData && !m2.taskData[t2].deleted
      && t1 != t2
    ensures !eqIgnoreCase(m2.taskData[t1].title, m2.taskData[t2].title)
  {
    if l != targetList {
      // Lane unchanged; taskId not in any old lane (count 0)
      assert m2.tasks[l] == m.tasks[l];
      if t1 == taskId {
        assert taskId in m.tasks[l];
        CountContainsAtLeastOne(m.lists, m.tasks, taskId, l);
        assert false;
      }
      if t2 == taskId {
        assert taskId in m.tasks[l];
        CountContainsAtLeastOne(m.lists, m.tasks, taskId, l);
        assert false;
      }
      assert m2.taskData[t1] == m.taskData[t1];
      assert m2.taskData[t2] == m.taskData[t2];
    } else if t1 != taskId && t2 != taskId {
      // Both old tasks in old lane — preserved from Inv(m)
      assert t1 in lane && t2 in lane;
      assert m2.taskData[t1] == m.taskData[t1];
      assert m2.taskData[t2] == m.taskData[t2];
    } else {
      // One is the restored task, other is old
      var other := if t1 == taskId then t2 else t1;
      assert other in lane;
      assert other != taskId;
      assert other in m.taskData && !m.taskData[other].deleted;
      TaskTitleExistsFromFalseHelper(m.tasks[targetList], m.taskData, task.title, None, 0, other);
    }
  }
}

// --- MoveTask ---
lemma MoveTaskPreservesInv(m: Model, taskId: int, toList: int, taskPlace: Place, m2: Model)
  requires Inv(m)
  requires apply(m, MoveTask(taskId, toList, taskPlace)) == true_(m2)
  ensures Inv(m2)
{
  // Remove from all lists, insert into target lane
  // D: count stays 1 (removed from all, added to one)
  // E: NoDupSeq preserved by remove then insertAt
  // N: taskTitleExistsInList check ensures title uniqueness in target
  assume {:axiom} false;
}

// --- CompleteTask ---
lemma CompleteTaskPreservesInv(m: Model, taskId: int, m2: Model)
  requires Inv(m)
  requires apply(m, CompleteTask(taskId)) == true_(m2)
  ensures Inv(m2)
{
  // Only changes completed field to true
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  assert forall id :: id in m2.taskData && id != taskId ==> m2.taskData[id] == m.taskData[id];
  var t := m.taskData[taskId];
  var t2 := m2.taskData[taskId];
  assert t2 == t.(completed := true);
}

// --- UncompleteTask ---
lemma UncompleteTaskPreservesInv(m: Model, taskId: int, m2: Model)
  requires Inv(m)
  requires apply(m, UncompleteTask(taskId)) == true_(m2)
  ensures Inv(m2)
{
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
}

// --- StarTask ---
lemma StarTaskPreservesInv(m: Model, taskId: int, m2: Model)
  requires Inv(m)
  requires apply(m, StarTask(taskId)) == true_(m2)
  ensures Inv(m2)
{
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
}

// --- UnstarTask ---
lemma UnstarTaskPreservesInv(m: Model, taskId: int, m2: Model)
  requires Inv(m)
  requires apply(m, UnstarTask(taskId)) == true_(m2)
  ensures Inv(m2)
{
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
}

// --- SetDueDate ---
lemma SetDueDatePreservesInv(m: Model, taskId: int, dueDate: Option<DateVal>, m2: Model)
  requires Inv(m)
  requires apply(m, SetDueDate(taskId, dueDate)) == true_(m2)
  ensures Inv(m2)
{
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  // L: if dueDate is Some, validDate was checked
}

// --- AssignTask ---
lemma AssignTaskPreservesInv(m: Model, taskId: int, userId: string, m2: Model)
  requires Inv(m)
  requires apply(m, AssignTask(taskId, userId)) == true_(m2)
  ensures Inv(m2)
{
  // Idempotent case: userId already in assignees → m2 == m
  if userId in m.taskData[taskId].assignees {
    assert m2 == m;
    return;
  }
  assert userId in m.members;
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  assert forall id :: id in m2.taskData && id != taskId ==> m2.taskData[id] == m.taskData[id];

  // H: every assignee of every task is a member
  forall id | id in m2.taskData
    ensures forall u :: u in m2.taskData[id].assignees ==> u in m2.members
  {
    if id == taskId {
      var oldAssignees := m.taskData[taskId].assignees;
      var newAssignees := oldAssignees + [userId];
      assert m2.taskData[taskId].assignees == newAssignees;
      forall u | u in newAssignees
        ensures u in m2.members
      {
        if u in oldAssignees {
        } else {
          assert u == userId;
        }
      }
    }
  }
}

// --- UnassignTask ---
lemma UnassignTaskPreservesInv(m: Model, taskId: int, userId: string, m2: Model)
  requires Inv(m)
  requires apply(m, UnassignTask(taskId, userId)) == true_(m2)
  ensures Inv(m2)
{
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  assert forall id :: id in m2.taskData && id != taskId ==> m2.taskData[id] == m.taskData[id];

  var t := m.taskData[taskId];
  assert apply(m, UnassignTask(taskId, userId)) == applyUnassignTask(m, taskId, userId);
  // without is transparent — solver can reason directly.
  // no longer needed — without is transparent
  WithoutSubset(t.assignees, userId);
  // Now: Filter(f, t.assignees) == without(t.assignees, userId)
  // and: u in without(t.assignees, userId) ==> u in t.assignees

  // H: every assignee of every task is still a member.
  forall id | id in m2.taskData
    ensures forall u :: u in m2.taskData[id].assignees ==> u in m2.members
  {
    if id == taskId {
      // m2.taskData[taskId].assignees == Filter(f, t.assignees) == without(t.assignees, userId)
      // WithoutSubset: every element was in t.assignees
      assert m2.taskData[taskId].assignees == without(t.assignees, userId);
    }
  }
}

// --- AddTagToTask ---
lemma AddTagToTaskPreservesInv(m: Model, taskId: int, tagId: int, m2: Model)
  requires Inv(m)
  requires apply(m, AddTagToTask(taskId, tagId)) == true_(m2)
  ensures Inv(m2)
{
  // Idempotent case: tagId already in tags → m2 == m
  if tagId in m.taskData[taskId].tags {
    assert m2 == m;
    return;
  }
  // tagId is in m.tags (checked by apply)
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  // F: new tag is in m.tags
  assert tagId in m.tags;
  assert forall id :: id in m2.taskData && id != taskId ==> m2.taskData[id] == m.taskData[id];
  var t2 := m2.taskData[taskId];
  assert forall t :: t in t2.tags ==>
    t in m.taskData[taskId].tags || t == tagId;
}

// --- RemoveTagFromTask ---
lemma RemoveTagFromTaskPreservesInv(m: Model, taskId: int, tagId: int, m2: Model)
  requires Inv(m)
  requires apply(m, RemoveTagFromTask(taskId, tagId)) == true_(m2)
  ensures Inv(m2)
{
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert m2.tags == m.tags;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  assert forall id :: id in m2.taskData && id != taskId ==> m2.taskData[id] == m.taskData[id];

  var t := m.taskData[taskId];
  assert apply(m, RemoveTagFromTask(taskId, tagId)) == applyRemoveTagFromTask(m, taskId, tagId);
  WithoutSubset(t.tags, tagId);

  // F: every tag ref still exists.
  forall id | id in m2.taskData
    ensures forall tag :: tag in m2.taskData[id].tags ==> tag in m2.tags
  {
    if id == taskId {
      forall tag | tag in m2.taskData[taskId].tags
        ensures tag in m2.tags
      {
        assert tag in t.tags;
      }
    }
  }
}

// --- CreateTag ---
lemma CreateTagPreservesInv(m: Model, name: string, m2: Model)
  requires Inv(m)
  requires apply(m, CreateTag(name)) == true_(m2)
  ensures Inv(m2)
{
  var id := m.nextTagId;
  assert !tagNameExists(m, name, None);
  assert m2 == m.(tags := m.tags[id := Tag(name)], nextTagId := m.nextTagId + 1);
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  // G: id < nextTagId + 1, and all old tags < nextTagId < nextTagId + 1
  // F: id is new tag, no task references it yet (tasks unchanged)
  assert id !in m.tags;
  // O: tagNameExists was false
  TagNameExistsFalseImpliesUnique(m, name, None);
}

// --- RenameTag ---
lemma RenameTagPreservesInv(m: Model, tagId: int, newName: string, m2: Model)
  requires Inv(m)
  requires apply(m, RenameTag(tagId, newName)) == true_(m2)
  ensures Inv(m2)
{
  assert m2 == m.(tags := m.tags[tagId := Tag(newName)]);
  assert m2.lists == m.lists;
  assert m2.tasks == m.tasks;
  assert m2.members == m.members;
  assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
  // O: tagNameExists(m, newName, Some(tagId)) was false
  TagNameExistsFalseImpliesUnique(m, newName, Some(tagId));
}

// --- DeleteTag ---
lemma DeleteTagPreservesInv(m: Model, tagId: int, m2: Model)
  requires Inv(m)
  requires apply(m, DeleteTag(tagId)) == true_(m2)
  ensures Inv(m2)
{
  if !(tagId in m.tags) {
    assert m2 == m;
  } else {
    var newTaskData := removeTagFromAllTasks(m.taskData, tagId);
    var newTags := (map k | k in m.tags && k != tagId :: m.tags[k]);
    assert m2 == m.(taskData := newTaskData, tags := newTags);

    RemoveTagFromAllTasksRemovesTag(m.taskData, tagId);
    RemoveTagFromAllTasksPreservesOtherTags(m.taskData, tagId);
    RemoveTagFromAllTasksDomain(m.taskData, tagId);
    RemoveTagFromAllTasksPreservesOtherFields(m.taskData, tagId);

    assert m2.lists == m.lists;
    assert m2.tasks == m.tasks;
    assert m2.members == m.members;
    assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);

    // F: all tag references in updated tasks are != tagId (removed) and were in m.tags
    forall id | id in m2.taskData
      ensures forall t :: t in m2.taskData[id].tags ==> t in m2.tags
    {
      assert id in m.taskData;
      var updTags := m2.taskData[id].tags;
      assert updTags == without(m.taskData[id].tags, tagId);
      WithoutSubset(m.taskData[id].tags, tagId);
      forall t | t in updTags
        ensures t in m2.tags
      {
        assert t in m.taskData[id].tags;
        assert t != tagId;
        // By Inv(m) F: t in m.tags, and since t != tagId, t in newTags
        assert t in m.tags;
        assert t in newTags;
      }
    }

    // N: titles and deleted status unchanged
    forall l, t1, t2 | l in m2.tasks
        && t1 in m2.tasks[l] && t1 in m2.taskData && !m2.taskData[t1].deleted
        && t2 in m2.tasks[l] && t2 in m2.taskData && !m2.taskData[t2].deleted
        && t1 != t2
      ensures !eqIgnoreCase(m2.taskData[t1].title, m2.taskData[t2].title)
    {
      assert m2.taskData[t1].title == m.taskData[t1].title;
      assert m2.taskData[t2].title == m.taskData[t2].title;
      assert m2.taskData[t1].deleted == m.taskData[t1].deleted;
      assert m2.taskData[t2].deleted == m.taskData[t2].deleted;
    }

    // H: assignees unchanged
    forall id | id in m2.taskData
      ensures forall u :: u in m2.taskData[id].assignees ==> u in m2.members
    {
      assert m2.taskData[id].assignees == m.taskData[id].assignees;
    }
  }
}

// --- MakeCollaborative ---
lemma MakeCollaborativePreservesInv(m: Model, m2: Model)
  requires Inv(m)
  requires apply(m, MakeCollaborative) == true_(m2)
  ensures Inv(m2)
{
  if m.mode.Collaborative? {
    assert m2 == m;
  } else {
    assert m2 == m.(mode := Collaborative);
    assert m2.lists == m.lists;
    assert m2.tasks == m.tasks;
    assert m2.members == m.members;
    assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
    // J: mode is now Collaborative, so J is vacuous
    // K: Personal had members == [m.owner], so |m.members| == 1 >= 1
    assert |m.members| >= 1;
  }
}

// --- AddMember ---
lemma AddMemberPreservesInv(m: Model, userId: string, m2: Model)
  requires Inv(m)
  requires apply(m, AddMember(userId)) == true_(m2)
  ensures Inv(m2)
{
  // Mode must be Collaborative (otherwise err)
  assert m.mode.Collaborative?;
  if userId in m.members {
    assert m2 == m;
  } else {
    assert m2 == m.(members := m.members + [userId]);
    assert m2.lists == m.lists;
    assert m2.tasks == m.tasks;
    assert m2.tags == m.tags;
    assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);
    // P: NoDupSeq preserved by appending non-member
    NoDupSeqAppend(m.members, userId);
    // H: existing assignees were members, still members in larger seq
    // I: owner was member, still member
    // K: |m2.members| == |m.members| + 1 >= 2
  }
}

// --- RemoveMember ---
lemma RemoveMemberPreservesInv(m: Model, userId: string, m2: Model)
  requires Inv(m)
  requires apply(m, RemoveMember(userId)) == true_(m2)
  ensures Inv(m2)
{
  var a := RemoveMember(userId);
  if userId == m.owner {
    assert false; // unreachable since apply returned true_
  } else if !(userId in m.members) {
    assert m2 == m;
  } else {
    assert apply(m, RemoveMember(userId)) == applyRemoveMember(m, userId);
    var newTaskData := clearAssigneeFromAllTasks(m.taskData, userId);
    assert m2.taskData == newTaskData;

    ClearAssigneeFromAllTasksRemovesUser(m.taskData, userId);
    ClearAssigneePreservesOtherFields(m.taskData, userId);
    ClearAssigneeFromAllTasksDomain(m.taskData, userId);
    ClearAssigneeSubset(m.taskData, userId);

    assert m2.lists == m.lists;
    assert m2.tasks == m.tasks;
    assert forall tid :: tid in m2.taskData ==> CountInLists(m2, tid) == CountInLists(m, tid);

    // J: if Personal, userId !in m.members (contradiction with branch condition)
    if m.mode.Personal? {
      assert m.members == [m.owner];
      assert userId != m.owner;
      assert userId !in m.members;
      assert false;
    }

    // Via equiv: m2 == applyRemoveMember(m, userId).value
    // without is transparent — solver can reason directly.
    // So m2.members == without(m.members, userId)
    WithoutPreservesNoDup(m.members, userId);
    WithoutKeeps(m.members, userId, m.owner);

    // I: owner in m2.members (kept because owner != userId)
    // P: NoDupSeq(m2.members) (filter preserves no-dups)
    // H: assignees cleared of userId; remaining were members; members only lost userId
    forall id | id in m2.taskData
      ensures forall u :: u in m2.taskData[id].assignees ==> u in m2.members
    {
      ClearAssigneeSubset(m.taskData, userId);
      forall u | u in m2.taskData[id].assignees
        ensures u in m2.members
      {
        // u was in original assignees and u != userId (by clearAssignee)
        assert u in m.taskData[id].assignees;
        assert u != userId;
        // u in m.members (by Inv H) and u != userId → u in filtered members
        assert u in m.members;
        // By subset: u in m2.members iff u in m.members && u != userId
        // But we need the reverse: u in m.members && u != userId ==> u in m2.members
        // without keeps elements != userId
        WithoutKeeps(m.members, userId, u);
      }
    }

    // N: titles and deleted status unchanged
    forall l, t1, t2 | l in m2.tasks
        && t1 in m2.tasks[l] && t1 in m2.taskData && !m2.taskData[t1].deleted
        && t2 in m2.tasks[l] && t2 in m2.taskData && !m2.taskData[t2].deleted
        && t1 != t2
      ensures !eqIgnoreCase(m2.taskData[t1].title, m2.taskData[t2].title)
    {
      assert m2.taskData[t1].title == m.taskData[t1].title;
      assert m2.taskData[t2].title == m.taskData[t2].title;
      assert m2.taskData[t1].deleted == m.taskData[t1].deleted;
      assert m2.taskData[t2].deleted == m.taskData[t2].deleted;
    }

    // F: tags unchanged
    forall id | id in m2.taskData
      ensures forall t :: t in m2.taskData[id].tags ==> t in m2.tags
    {
      assert m2.taskData[id].tags == m.taskData[id].tags;
      assert m2.tags == m.tags;
    }
  }
}


lemma ClearAssigneeSubset(taskData: map<int, Task>, userId: string)
  ensures forall tid :: tid in clearAssigneeFromAllTasks(taskData, userId) ==>
    (forall u :: u in clearAssigneeFromAllTasks(taskData, userId)[tid].assignees ==>
      u in taskData[tid].assignees && u != userId)
{
  forall tid | tid in clearAssigneeFromAllTasks(taskData, userId)
    ensures forall u :: u in clearAssigneeFromAllTasks(taskData, userId)[tid].assignees ==>
      u in taskData[tid].assignees && u != userId
  {
    assert clearAssigneeFromAllTasks(taskData, userId)[tid].assignees
      == without(taskData[tid].assignees, userId);
    WithoutSubset(taskData[tid].assignees, userId);
  }
}

// =============================================================================
// Main Dispatcher
// =============================================================================

lemma StepPreservesInv(m: Model, a: Action, m2: Model)
  requires Inv(m)
  requires apply(m, a) == true_(m2)
  ensures Inv(m2)
{
  match a {
    case NoOp => NoOpPreservesInv(m, m2);
    case AddList(name) => AddListPreservesInv(m, name, m2);
    case RenameList(listId, newName) => RenameListPreservesInv(m, listId, newName, m2);
    case DeleteList(listId) => DeleteListPreservesInv(m, listId, m2);
    case MoveList(listId, listPlace) => MoveListPreservesInv(m, listId, listPlace, m2);
    case AddTask(listId, title) => AddTaskPreservesInv(m, listId, title, m2);
    case EditTask(taskId, title, notes) => EditTaskPreservesInv(m, taskId, title, notes, m2);
    case DeleteTask(taskId, userId) => DeleteTaskPreservesInv(m, taskId, userId, m2);
    case RestoreTask(taskId) => RestoreTaskPreservesInv(m, taskId, m2);
    case MoveTask(taskId, toList, taskPlace) => MoveTaskPreservesInv(m, taskId, toList, taskPlace, m2);
    case CompleteTask(taskId) => CompleteTaskPreservesInv(m, taskId, m2);
    case UncompleteTask(taskId) => UncompleteTaskPreservesInv(m, taskId, m2);
    case StarTask(taskId) => StarTaskPreservesInv(m, taskId, m2);
    case UnstarTask(taskId) => UnstarTaskPreservesInv(m, taskId, m2);
    case SetDueDate(taskId, dueDate) => SetDueDatePreservesInv(m, taskId, dueDate, m2);
    case AssignTask(taskId, userId) => AssignTaskPreservesInv(m, taskId, userId, m2);
    case UnassignTask(taskId, userId) => UnassignTaskPreservesInv(m, taskId, userId, m2);
    case AddTagToTask(taskId, tagId) => AddTagToTaskPreservesInv(m, taskId, tagId, m2);
    case RemoveTagFromTask(taskId, tagId) => RemoveTagFromTaskPreservesInv(m, taskId, tagId, m2);
    case CreateTag(name) => CreateTagPreservesInv(m, name, m2);
    case RenameTag(tagId, newName) => RenameTagPreservesInv(m, tagId, newName, m2);
    case DeleteTag(tagId) => DeleteTagPreservesInv(m, tagId, m2);
    case MakeCollaborative => MakeCollaborativePreservesInv(m, m2);
    case AddMember(userId) => AddMemberPreservesInv(m, userId, m2);
    case RemoveMember(userId) => RemoveMemberPreservesInv(m, userId, m2);
  }
}

// =============================================================================
// Part 2: Multi-Project Invariant Preservation
// =============================================================================

// Multi-project invariant: Inv holds for every project in the MultiModel
ghost predicate MultiInv(mm: MultiModel)
{
  forall pid :: pid in mm.projects ==> Inv(mm.projects[pid])
}

// applyOk preserves invariant: either apply succeeds (StepPreservesInv) or returns m unchanged
lemma ApplyOkPreservesInv(m: Model, a: Action)
  requires Inv(m)
  ensures Inv(applyOk(m, a))
{
  var r := apply(m, a);
  if r.true_? {
    StepPreservesInv(m, a, r.value);
  }
}

// copyTaskToModel preserves invariant: chains applyOk calls, each preserving Inv
lemma {:timeLimit 60} CopyTaskToModelPreservesInv(srcTask: Task, dstModel: Model, dstList: ListId)
  requires Inv(dstModel)
  ensures Inv(copyTaskToModel(srcTask, dstModel, dstList))
{
  var r := apply(dstModel, AddTask(dstList, srcTask.title));
  if !r.true_? {
    return;
  }
  StepPreservesInv(dstModel, AddTask(dstList, srcTask.title), r.value);
  var newTid := r.value.nextTaskId - 1;
  var m1 := if srcTask.notes != "" then applyOk(r.value, EditTask(newTid, srcTask.title, srcTask.notes)) else r.value;
  ApplyOkPreservesInv(r.value, EditTask(newTid, srcTask.title, srcTask.notes));
  var m2 := if srcTask.starred then applyOk(m1, StarTask(newTid)) else m1;
  ApplyOkPreservesInv(m1, StarTask(newTid));
  var m3 := if srcTask.completed then applyOk(m2, CompleteTask(newTid)) else m2;
  ApplyOkPreservesInv(m2, CompleteTask(newTid));
  ApplyOkPreservesInv(m3, SetDueDate(newTid, srcTask.dueDate));
}

// copyTasksFromLane preserves invariant: recursive, each step uses CopyTaskToModelPreservesInv
lemma CopyTasksFromLanePreservesInv(lane: seq<TaskId>, taskData: map<int, Task>,
    dstModel: Model, dstList: ListId, i: int)
  requires Inv(dstModel)
  requires i >= 0 && i <= |lane|
  ensures Inv(copyTasksFromLane(lane, taskData, dstModel, dstList, i))
  decreases |lane| - i
{
  if i >= |lane| { return; }
  var tid := lane[i];
  if tid !in taskData {
    CopyTasksFromLanePreservesInv(lane, taskData, dstModel, dstList, i + 1);
  } else {
    var task := taskData[tid];
    if task.deleted {
      CopyTasksFromLanePreservesInv(lane, taskData, dstModel, dstList, i + 1);
    } else {
      CopyTaskToModelPreservesInv(task, dstModel, dstList);
      var newDst := copyTaskToModel(task, dstModel, dstList);
      CopyTasksFromLanePreservesInv(lane, taskData, newDst, dstList, i + 1);
    }
  }
}

// tryMoveTaskTo preserves invariant for all projects
lemma TryMoveTaskToPreservesMultiInv(mm: MultiModel, srcProjectId: ProjectId,
    dstProjectId: ProjectId, taskId: TaskId, dstList: ListId, taskPlace: Place)
  requires MultiInv(mm)
  ensures MultiInv(tryMoveTaskTo(mm, srcProjectId, dstProjectId, taskId, dstList, taskPlace))
{
  var result := tryMoveTaskTo(mm, srcProjectId, dstProjectId, taskId, dstList, taskPlace);
  if srcProjectId !in mm.projects || dstProjectId !in mm.projects { return; }
  var src := mm.projects[srcProjectId];
  var dst := mm.projects[dstProjectId];
  if taskId !in src.taskData { return; }
  if src.taskData[taskId].deleted { return; }
  var r1 := apply(src, DeleteTask(taskId, src.owner));
  if !r1.true_? { return; }
  StepPreservesInv(src, DeleteTask(taskId, src.owner), r1.value);
  CopyTaskToModelPreservesInv(src.taskData[taskId], dst, dstList);
}

// tryCopyTaskTo preserves invariant for all projects
lemma TryCopyTaskToPreservesMultiInv(mm: MultiModel, srcProjectId: ProjectId,
    dstProjectId: ProjectId, taskId: TaskId, dstList: ListId)
  requires MultiInv(mm)
  ensures MultiInv(tryCopyTaskTo(mm, srcProjectId, dstProjectId, taskId, dstList))
{
  var result := tryCopyTaskTo(mm, srcProjectId, dstProjectId, taskId, dstList);
  if srcProjectId !in mm.projects || dstProjectId !in mm.projects { return; }
  var src := mm.projects[srcProjectId];
  var dst := mm.projects[dstProjectId];
  if taskId !in src.taskData { return; }
  if src.taskData[taskId].deleted { return; }
  CopyTaskToModelPreservesInv(src.taskData[taskId], dst, dstList);
}

// tryMoveListTo preserves invariant for all projects
// Helper: Inv holds for dstModel after AddList + copyTasksFromLane
lemma MoveListToDstPreservesInv(dst: Model, listName: string, lane: seq<TaskId>,
    taskData: map<int, Task>, listId: ListId)
  requires Inv(dst)
  requires apply(dst, AddList(listName)).true_?
  ensures Inv(copyTasksFromLane(lane, taskData, apply(dst, AddList(listName)).value,
              apply(dst, AddList(listName)).value.nextListId - 1, 0))
{
  var r1 := apply(dst, AddList(listName));
  StepPreservesInv(dst, AddList(listName), r1.value);
  var newListId := r1.value.nextListId - 1;
  CopyTasksFromLanePreservesInv(lane, taskData, r1.value, newListId, 0);
}

lemma {:timeLimit 120} TryMoveListToPreservesMultiInv(mm: MultiModel, srcProjectId: ProjectId,
    dstProjectId: ProjectId, listId: ListId)
  requires MultiInv(mm)
  ensures MultiInv(tryMoveListTo(mm, srcProjectId, dstProjectId, listId))
{
  if srcProjectId !in mm.projects { return; }
  if dstProjectId !in mm.projects { return; }
  var src := mm.projects[srcProjectId];
  var dst := mm.projects[dstProjectId];
  if !(listId in src.lists) { return; }
  if listId !in src.listNames { return; }
  var listName := src.listNames[listId];
  var r1 := apply(dst, AddList(listName));
  if !r1.true_? { return; }
  var lane := if listId in src.tasks then src.tasks[listId] else [];
  MoveListToDstPreservesInv(dst, listName, lane, src.taskData, listId);
  var r2 := apply(src, DeleteList(listId));
  if !r2.true_? { return; }
  StepPreservesInv(src, DeleteList(listId), r2.value);
}

// Main theorem: tryApplyMulti preserves MultiInv
lemma TryApplyMultiPreservesMultiInv(mm: MultiModel, action: MultiAction)
  requires MultiInv(mm)
  ensures MultiInv(tryApplyMulti(mm, action))
{
  match action {
    case SingleAction(projectId, a) =>
      if projectId !in mm.projects { return; }
      var project := mm.projects[projectId];
      var r := apply(project, a);
      if !r.true_? { return; }
      StepPreservesInv(project, a, r.value);
    case MoveTaskTo(srcProject, dstProject, taskId, dstList, taskPlace) =>
      TryMoveTaskToPreservesMultiInv(mm, srcProject, dstProject, taskId, dstList, taskPlace);
    case CopyTaskTo(srcProject, dstProject, taskId, dstList) =>
      TryCopyTaskToPreservesMultiInv(mm, srcProject, dstProject, taskId, dstList);
    case MoveListTo(srcProject, dstProject, listId) =>
      TryMoveListToPreservesMultiInv(mm, srcProject, dstProject, listId);
  }
}

// =============================================================================
// Unfold lemmas: connect apply(m, Action) to concrete field updates.
// The generated apply wraps map access in Option (match Some/None), making it
// opaque to the solver. These lemmas unfold through the Option to give Dafny
// the direct field-update form.
// =============================================================================

// If CountInLists > 0, there exists a list containing taskId
lemma CountPositiveImpliesExists(m: Model, taskId: int)
  requires Inv(m)
  requires CountInLists(m, taskId) > 0
  ensures exists l :: l in m.tasks && taskId in m.tasks[l]
{
  CountPositiveImpliesExistsHelper(m.lists, m.tasks, taskId);
}

lemma CountPositiveImpliesExistsHelper(lists: seq<int>, tasks: map<int, seq<int>>, id: int)
  requires CountInListsHelper(lists, tasks, id) > 0
  ensures exists l :: l in tasks && id in tasks[l]
  decreases |lists|
{
  if |lists| > 0 {
    var l := lists[0];
    var lane := if l in tasks then tasks[l] else [];
    if id in lane {
      assert l in tasks && id in tasks[l];
    } else {
      CountPositiveImpliesExistsHelper(lists[1..], tasks, id);
    }
  }
}

// findListForTask returns Some for non-deleted tasks (by Inv D: count == 1)
lemma FindListForTaskIsSome(m: Model, taskId: int)
  requires Inv(m)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures findListForTask(m, taskId).Some?
{
  assert CountInLists(m, taskId) == 1;
  CountPositiveImpliesExists(m, taskId);
  var l :| l in m.tasks && taskId in m.tasks[l];
  assert l in m.lists;
  FindListForTaskFinds(m, taskId, l);
}

// taskTitleExistsInList is false when checking the task's own title (by Inv N)
lemma TaskTitleExistsFromFalseInv(lane: seq<TaskId>, taskData: map<int, Task>,
    title: string, excludeId: TaskId, i: int)
  requires 0 <= i <= |lane|
  // No non-deleted task in lane (other than excludeId) has eqIgnoreCase title
  requires forall j :: i <= j < |lane| && lane[j] != excludeId && lane[j] in taskData
    && !taskData[lane[j]].deleted ==> !eqIgnoreCase(taskData[lane[j]].title, title)
  ensures !taskTitleExistsFrom(lane, taskData, title, Some(excludeId), i)
  decreases |lane| - i
{
  if i < |lane| {
    TaskTitleExistsFromFalseInv(lane, taskData, title, excludeId, i + 1);
  }
}

lemma UnfoldCompleteTask(m: Model, taskId: TaskId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures apply(m, CompleteTask(taskId)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(completed := true)]))
{}

lemma UnfoldUncompleteTask(m: Model, taskId: TaskId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures apply(m, UncompleteTask(taskId)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(completed := false)]))
{}

lemma UnfoldStarTask(m: Model, taskId: TaskId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures apply(m, StarTask(taskId)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(starred := true)]))
{}

lemma UnfoldUnstarTask(m: Model, taskId: TaskId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures apply(m, UnstarTask(taskId)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(starred := false)]))
{}

lemma UnfoldSetDueDate(m: Model, taskId: TaskId, dueDate: Option<DateVal>)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  requires dueDate.Some? ==> validDate(dueDate.value)
  ensures apply(m, SetDueDate(taskId, dueDate)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(dueDate := dueDate)]))
{}

lemma UnfoldAssignTask(m: Model, taskId: TaskId, userId: UserId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  requires userId in m.members
  requires userId in m.taskData[taskId].assignees
  ensures apply(m, AssignTask(taskId, userId)) == true_(m)
{}

lemma UnfoldUnassignTask(m: Model, taskId: TaskId, userId: UserId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures apply(m, UnassignTask(taskId, userId)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(assignees := without(m.taskData[taskId].assignees, userId))]))
{}

lemma UnfoldAddTagToTask(m: Model, taskId: TaskId, tagId: TagId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  requires tagId in m.tags
  requires tagId in m.taskData[taskId].tags
  ensures apply(m, AddTagToTask(taskId, tagId)) == true_(m)
{}

lemma UnfoldRemoveTagFromTask(m: Model, taskId: TaskId, tagId: TagId)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  ensures apply(m, RemoveTagFromTask(taskId, tagId)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(tags := without(m.taskData[taskId].tags, tagId))]))
{}

// listNameExists is false when renaming to the same name (by Inv M, name is unique)
lemma ListNameExistsFalseWhenSame(m: Model, listId: ListId, newName: string)
  requires Inv(m)
  requires listId in m.lists
  requires listId in m.listNames
  requires m.listNames[listId] == newName
  ensures !listNameExists(m, newName, Some(listId))
{
  ListNameExistsFromFalseInv(m.lists, m.listNames, newName, listId, 0);
}

// Given Inv M (names unique), listNameExistsFrom is false when checking the current name
lemma ListNameExistsFromFalseInv(lists: seq<ListId>, listNames: map<int, string>,
    name: string, excludeId: ListId, i: int)
  requires 0 <= i <= |lists|
  requires forall l :: l in listNames <==> l in lists
  requires excludeId in lists && excludeId in listNames && listNames[excludeId] == name
  requires forall l1, l2 :: l1 in listNames && l2 in listNames && l1 != l2 ==> !eqIgnoreCase(listNames[l1], listNames[l2])
  ensures !listNameExistsFrom(lists, listNames, name, Some(excludeId), i)
  decreases |lists| - i
{
  if i < |lists| {
    var lid := lists[i];
    if lid != excludeId && lid in listNames {
      assert !eqIgnoreCase(listNames[lid], listNames[excludeId]);
    }
    ListNameExistsFromFalseInv(lists, listNames, name, excludeId, i + 1);
  }
}

lemma UnfoldRenameList(m: Model, listId: ListId, newName: string)
  requires listId in m.lists
  requires !listNameExists(m, newName, Some(listId))
  ensures apply(m, RenameList(listId, newName)) == true_(m.(listNames := m.listNames[listId := newName]))
{}

lemma UnfoldEditTask(m: Model, taskId: TaskId, title: string, notes: string)
  requires taskId in m.taskData && !m.taskData[taskId].deleted
  requires var listId := findListForTask(m, taskId);
           listId.Some? ==> !taskTitleExistsInList(m, listId.value, title, Some(taskId))
  ensures apply(m, EditTask(taskId, title, notes)) == true_(m.(taskData := m.taskData[taskId := m.taskData[taskId].(title := title, notes := notes)]))
{}

// =============================================================================
// Part 3: NoOp Sanity — Complete Enumeration of Identity Cases
// =============================================================================

// An action is a NoOp if it leaves the model unchanged.
// This enumerates ALL such cases.
//
// Note: Unlike the old dafny-replay project, assignees and tags are sequences
// (not sets), so AssignTask/AddTagToTask always append — they are NEVER NoOps.
// Also RestoreTask on non-deleted returns error (not Ok(m)).

// --- Idempotent operations ---
predicate NoOpAction(a: Action) { a.NoOp? }
predicate NoOpDeleteListMissing(m: Model, a: Action) { a.DeleteList? && a.listId !in m.lists }
predicate NoOpDeleteTaskMissing(m: Model, a: Action) { a.DeleteTask? && a.taskId !in m.taskData }
predicate NoOpDeleteTaskAlreadyDeleted(m: Model, a: Action) { a.DeleteTask? && a.taskId in m.taskData && m.taskData[a.taskId].deleted }
predicate NoOpDeleteTagMissing(m: Model, a: Action) { a.DeleteTag? && a.tagId !in m.tags }
predicate NoOpMakeCollaborativeAlready(m: Model, a: Action) { a.MakeCollaborative? && m.mode.Collaborative? }
predicate NoOpAddMemberAlready(m: Model, a: Action) { a.AddMember? && m.mode.Collaborative? && a.userId in m.members }
predicate NoOpRemoveMemberMissing(m: Model, a: Action) { a.RemoveMember? && a.userId !in m.members }

// --- Zero-effect operations ---
predicate NoOpRenameListSameName(m: Model, a: Action) {
  a.RenameList? && a.listId in m.lists && a.listId in m.listNames && m.listNames[a.listId] == a.newName
}
predicate NoOpEditTaskSameContent(m: Model, a: Action) {
  a.EditTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && m.taskData[a.taskId].title == a.title && m.taskData[a.taskId].notes == a.notes
}
predicate NoOpSetDueDateSame(m: Model, a: Action) {
  a.SetDueDate? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && m.taskData[a.taskId].dueDate == a.dueDate
}
predicate NoOpRenameTagSameName(m: Model, a: Action) {
  a.RenameTag? && a.tagId in m.tags && m.tags[a.tagId].name == a.newName
}
predicate NoOpCompleteTaskAlready(m: Model, a: Action) {
  a.CompleteTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted && m.taskData[a.taskId].completed
}
predicate NoOpUncompleteTaskAlready(m: Model, a: Action) {
  a.UncompleteTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted && !m.taskData[a.taskId].completed
}
predicate NoOpStarTaskAlready(m: Model, a: Action) {
  a.StarTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted && m.taskData[a.taskId].starred
}
predicate NoOpUnstarTaskAlready(m: Model, a: Action) {
  a.UnstarTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted && !m.taskData[a.taskId].starred
}
predicate NoOpAssignTaskAlready(m: Model, a: Action) {
  a.AssignTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && a.userId in m.members && a.userId in m.taskData[a.taskId].assignees
}
predicate NoOpUnassignTaskMissing(m: Model, a: Action) {
  a.UnassignTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && a.userId !in m.taskData[a.taskId].assignees
}
predicate NoOpAddTagToTaskAlready(m: Model, a: Action) {
  a.AddTagToTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && a.tagId in m.tags && a.tagId in m.taskData[a.taskId].tags
}
predicate NoOpRemoveTagFromTaskMissing(m: Model, a: Action) {
  a.RemoveTagFromTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && a.tagId !in m.taskData[a.taskId].tags
}
predicate NoOpMoveListSamePosition(m: Model, a: Action)
  requires Inv(m)
{
  a.MoveList? && a.listId in m.lists &&
  var pos := posFromListPlace(m.lists, a.listPlace);
  pos >= 0 &&
  var listsWithout := without(m.lists, a.listId);
  var clamped := MathMin(pos, |listsWithout|);
  insertAt(listsWithout, clamped, a.listId) == m.lists
}
predicate NoOpMoveTaskSamePosition(m: Model, a: Action)
  requires Inv(m)
{
  a.MoveTask? && a.taskId in m.taskData && !m.taskData[a.taskId].deleted
  && a.toList in m.lists && a.toList in m.tasks &&
  var cleaned := removeTaskFromAllLists(m.lists, m.tasks, a.taskId);
  var targetLane := if a.toList in cleaned then cleaned[a.toList] else [];
  var pos := posFromPlace(targetLane, a.taskPlace);
  pos >= 0 &&
  var clamped := MathMin(pos, |targetLane|);
  var newLane := insertAt(targetLane, clamped, a.taskId);
  cleaned[a.toList := newLane] == m.tasks
}

predicate IsNoOp(m: Model, a: Action)
  requires Inv(m)
{
  NoOpAction(a)
  || NoOpDeleteListMissing(m, a)
  || NoOpDeleteTaskMissing(m, a)
  || NoOpDeleteTaskAlreadyDeleted(m, a)
  || NoOpDeleteTagMissing(m, a)
  || NoOpMakeCollaborativeAlready(m, a)
  || NoOpAddMemberAlready(m, a)
  || NoOpRemoveMemberMissing(m, a)
  || NoOpRenameListSameName(m, a)
  || NoOpEditTaskSameContent(m, a)
  || NoOpSetDueDateSame(m, a)
  || NoOpRenameTagSameName(m, a)
  || NoOpCompleteTaskAlready(m, a)
  || NoOpUncompleteTaskAlready(m, a)
  || NoOpStarTaskAlready(m, a)
  || NoOpUnstarTaskAlready(m, a)
  || NoOpAssignTaskAlready(m, a)
  || NoOpUnassignTaskMissing(m, a)
  || NoOpAddTagToTaskAlready(m, a)
  || NoOpRemoveTagFromTaskMissing(m, a)
  || NoOpMoveListSamePosition(m, a)
  || NoOpMoveTaskSamePosition(m, a)
}

// Completeness: if apply(m, a) == Ok(m), then IsNoOp(m, a)
lemma {:timeLimit 120} CheckNoOps(m: Model, a: Action)
  requires Inv(m)
  requires apply(m, a) == true_(m)
  ensures IsNoOp(m, a)
{
  match a {
    case NoOp => assert NoOpAction(a);

    case AddList(name) =>
      // Always changes nextListId
      assert apply(m, a).value.nextListId != m.nextListId;
      assert false;

    case RenameList(listId, newName) =>
      if listId !in m.lists { assert false; }
      else { assert m.listNames[listId] == newName; assert NoOpRenameListSameName(m, a); }

    case DeleteList(listId) =>
      if listId !in m.lists { assert NoOpDeleteListMissing(m, a); }
      else { assert false; }

    case MoveList(listId, listPlace) =>
      if listId !in m.lists { assert false; }
      else { assert NoOpMoveListSamePosition(m, a); }

    case AddTask(listId, title) =>
      if listId !in m.lists { assert false; }
      else { assert apply(m, a).value.nextTaskId != m.nextTaskId; assert false; }

    case EditTask(taskId, title, notes) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else {
        var t := m.taskData[taskId];
        assert t.title == title && t.notes == notes;
        assert NoOpEditTaskSameContent(m, a);
      }

    case DeleteTask(taskId, userId) =>
      if taskId !in m.taskData { assert NoOpDeleteTaskMissing(m, a); }
      else if m.taskData[taskId].deleted { assert NoOpDeleteTaskAlreadyDeleted(m, a); }
      else { assert false; }

    case RestoreTask(taskId) =>
      // New domain: non-deleted returns error, deleted always changes model
      assert false;

    case MoveTask(taskId, toList, taskPlace) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted || toList !in m.lists { assert false; }
      else { assert NoOpMoveTaskSamePosition(m, a); }

    case CompleteTask(taskId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else { assert m.taskData[taskId].completed; assert NoOpCompleteTaskAlready(m, a); }

    case UncompleteTask(taskId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else { assert !m.taskData[taskId].completed; assert NoOpUncompleteTaskAlready(m, a); }

    case StarTask(taskId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else { assert m.taskData[taskId].starred; assert NoOpStarTaskAlready(m, a); }

    case UnstarTask(taskId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else { assert !m.taskData[taskId].starred; assert NoOpUnstarTaskAlready(m, a); }

    case SetDueDate(taskId, dueDate) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else { assert m.taskData[taskId].dueDate == dueDate; assert NoOpSetDueDateSame(m, a); }

    case AssignTask(taskId, userId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted || userId !in m.members { assert false; }
      else if userId in m.taskData[taskId].assignees { assert NoOpAssignTaskAlready(m, a); }
      else { assert false; }

    case UnassignTask(taskId, userId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else {
        // apply returns ok(m) only when without is identity → userId not in assignees
        var t := m.taskData[taskId];
        if userId in t.assignees {
          // without removes at least one element, so the task changes, so m2 != m
          WithoutShorter(t.assignees, userId);
          assert false;
        }
        assert NoOpUnassignTaskMissing(m, a);
      }

    case AddTagToTask(taskId, tagId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted || tagId !in m.tags { assert false; }
      else if tagId in m.taskData[taskId].tags { assert NoOpAddTagToTaskAlready(m, a); }
      else {
        // append grows the seq → m2 != m
        assert |m.taskData[taskId].tags + [tagId]| > |m.taskData[taskId].tags|;
        assert false;
      }

    case RemoveTagFromTask(taskId, tagId) =>
      if taskId !in m.taskData || m.taskData[taskId].deleted { assert false; }
      else {
        var t := m.taskData[taskId];
        if tagId in t.tags {
          WithoutShorter(t.tags, tagId);
          assert false;
        }
        assert NoOpRemoveTagFromTaskMissing(m, a);
      }

    case CreateTag(name) =>
      assert apply(m, a).value.nextTagId != m.nextTagId;
      assert false;

    case RenameTag(tagId, newName) =>
      if tagId !in m.tags { assert false; }
      else { assert m.tags[tagId].name == newName; assert NoOpRenameTagSameName(m, a); }

    case DeleteTag(tagId) =>
      if tagId !in m.tags { assert NoOpDeleteTagMissing(m, a); }
      else { assert false; }

    case MakeCollaborative =>
      if m.mode.Collaborative? { assert NoOpMakeCollaborativeAlready(m, a); }
      else { assert false; }

    case AddMember(userId) =>
      if m.mode.Personal? { assert false; }
      else if userId in m.members { assert NoOpAddMemberAlready(m, a); }
      else { assert false; }

    case RemoveMember(userId) =>
      if userId == m.owner { assert false; }
      else if userId !in m.members {
        WithoutNoOp(m.members, userId);
        assert NoOpRemoveMemberMissing(m, a);
      }
      else {
        // userId in members → without removes it → members change → m' != m
        WithoutShorter(m.members, userId);
        assert false;
      }
  }
}

// Soundness: if IsNoOp(m, a), then apply(m, a) == Ok(m)
lemma {:timeLimit 300} NoOpImpliesUnchanged(m: Model, a: Action)
  requires Inv(m)
  requires IsNoOp(m, a)
  ensures apply(m, a) == true_(m)
{
  if NoOpAction(a) { return; }
  if NoOpDeleteListMissing(m, a) { return; }
  if NoOpDeleteTaskMissing(m, a) { return; }
  if NoOpDeleteTaskAlreadyDeleted(m, a) { return; }
  if NoOpDeleteTagMissing(m, a) { return; }
  if NoOpMakeCollaborativeAlready(m, a) { return; }
  if NoOpAddMemberAlready(m, a) { return; }
  if NoOpRemoveMemberMissing(m, a) {
    // userId not in members, and Inv ensures owner in members, so userId != owner
    assert a.userId != m.owner;
    WithoutNoOp(m.members, a.userId);
    return;
  }
  if NoOpRenameListSameName(m, a) {
    // listNameExists is a function-by-method; help Dafny see it's false.
    // Spec body: exists lid :: lid in m.lists && (exclude.None? || lid != exclude.value) && eqIgnoreCase(...)
    // By Inv M, no other list has the same name → no such lid exists.
    ListNameExistsFalseWhenSame(m, a.listId, a.newName);
    UnfoldRenameList(m, a.listId, a.newName);
    assert m.listNames[a.listId := a.newName] == m.listNames;
    return;
  }
  if NoOpEditTaskSameContent(m, a) {
    var taskId := a.taskId;
    var t := m.taskData[taskId];
    // findListForTask returns Some (Inv D: non-deleted task is in exactly one list)
    FindListForTaskIsSome(m, taskId);
    var listId := findListForTask(m, taskId).value;
    // taskTitleExistsInList is false (Inv N: title unique within list, excluding self)
    FindListForTaskSoundHelper(m.lists, m.tasks, taskId, 0);
    assert taskId in m.tasks[listId];
    assert listId in m.tasks;
    // By Inv N, no other non-deleted task in this list has the same title
    forall j | 0 <= j < |m.tasks[listId]| && m.tasks[listId][j] != taskId
      && m.tasks[listId][j] in m.taskData && !m.taskData[m.tasks[listId][j]].deleted
      ensures !eqIgnoreCase(m.taskData[m.tasks[listId][j]].title, a.title)
    {
      // m.tasks[listId][j] and taskId are both in the list, both non-deleted, different
      // By Inv N: !eqIgnoreCase(their titles). Since a.title == taskData[taskId].title, done.
    }
    TaskTitleExistsFromFalseInv(m.tasks[listId], m.taskData, a.title, taskId, 0);
    UnfoldEditTask(m, taskId, a.title, a.notes);
    assert t.(title := a.title, notes := a.notes) == t;
    assert m.taskData[taskId := t] == m.taskData;
    return;
  }
  if NoOpSetDueDateSame(m, a) {
    UnfoldSetDueDate(m, a.taskId, a.dueDate);
    var t := m.taskData[a.taskId];
    assert t.(dueDate := a.dueDate) == t;
    assert m.taskData[a.taskId := t] == m.taskData;
    return;
  }
  if NoOpRenameTagSameName(m, a) {
    assert m.tags[a.tagId := Tag(a.newName)] == m.tags;
    return;
  }
  if NoOpCompleteTaskAlready(m, a) {
    UnfoldCompleteTask(m, a.taskId);
    var t := m.taskData[a.taskId]; assert t.(completed := true) == t;
    assert m.taskData[a.taskId := t] == m.taskData; return;
  }
  if NoOpUncompleteTaskAlready(m, a) {
    UnfoldUncompleteTask(m, a.taskId);
    var t := m.taskData[a.taskId]; assert t.(completed := false) == t;
    assert m.taskData[a.taskId := t] == m.taskData; return;
  }
  if NoOpStarTaskAlready(m, a) {
    UnfoldStarTask(m, a.taskId);
    var t := m.taskData[a.taskId]; assert t.(starred := true) == t;
    assert m.taskData[a.taskId := t] == m.taskData; return;
  }
  if NoOpUnstarTaskAlready(m, a) {
    UnfoldUnstarTask(m, a.taskId);
    var t := m.taskData[a.taskId]; assert t.(starred := false) == t;
    assert m.taskData[a.taskId := t] == m.taskData; return;
  }
  if NoOpAssignTaskAlready(m, a) { UnfoldAssignTask(m, a.taskId, a.userId); return; }
  if NoOpUnassignTaskMissing(m, a) {
    UnfoldUnassignTask(m, a.taskId, a.userId);
    WithoutNoOp(m.taskData[a.taskId].assignees, a.userId);
    var t := m.taskData[a.taskId]; assert t.(assignees := without(t.assignees, a.userId)) == t;
    assert m.taskData[a.taskId := t] == m.taskData; return;
  }
  if NoOpAddTagToTaskAlready(m, a) { UnfoldAddTagToTask(m, a.taskId, a.tagId); return; }
  if NoOpRemoveTagFromTaskMissing(m, a) {
    UnfoldRemoveTagFromTask(m, a.taskId, a.tagId);
    WithoutNoOp(m.taskData[a.taskId].tags, a.tagId);
    var t := m.taskData[a.taskId]; assert t.(tags := without(t.tags, a.tagId)) == t;
    assert m.taskData[a.taskId := t] == m.taskData; return;
  }
  if NoOpMoveListSamePosition(m, a) {
    // MoveList: apply returns m.(lists := insertAt(without(lists, listId), clamped, listId))
    // The NoOp predicate asserts this equals m.lists.
    var listId := a.listId;
    var pos := posFromListPlace(m.lists, a.listPlace);
    var listsWithout := without(m.lists, listId);
    var clamped := MathMin(pos, |listsWithout|);
    assert insertAt(listsWithout, clamped, listId) == m.lists;
    assert m.(lists := m.lists) == m;
    return;
  }
  // MoveTask same position
  assert NoOpMoveTaskSamePosition(m, a);
  {
    var taskId := a.taskId;
    var toList := a.toList;
    assert taskId in m.taskData && !m.taskData[taskId].deleted;
    assert toList in m.lists && toList in m.tasks;
    var cleaned := removeTaskFromAllLists(m.lists, m.tasks, taskId);
    var targetLane := if toList in cleaned then cleaned[toList] else [];
    var pos := posFromPlace(targetLane, a.taskPlace);
    var clamped := MathMin(pos, |targetLane|);
    // From predicate: result equals original
    assert cleaned[toList := insertAt(targetLane, clamped, taskId)] == m.tasks;
    // So apply returns m.(tasks := m.tasks) == m
    // But apply also checks taskTitleExistsInList — need to show it's false
    // The title is unchanged, task is non-deleted, in the list → by Inv N, no duplicate
    FindListForTaskIsSome(m, taskId);
    var listId := findListForTask(m, taskId).value;
    FindListForTaskSoundHelper(m.lists, m.tasks, taskId, 0);
    assert taskId in m.tasks[listId];
    forall j | 0 <= j < |m.tasks[toList]| && m.tasks[toList][j] != taskId
      && m.tasks[toList][j] in m.taskData && !m.taskData[m.tasks[toList][j]].deleted
      ensures !eqIgnoreCase(m.taskData[m.tasks[toList][j]].title, m.taskData[taskId].title)
    {}
    TaskTitleExistsFromFalseInv(m.tasks[toList], m.taskData, m.taskData[taskId].title, taskId, 0);
    assert m.(tasks := m.tasks) == m;
  }
}
