---
name: dont-overwrite-schematest
description: "Never overwrite user's SchemaTest.lean changes — always re-read the main tree version before editing"
metadata: 
  node_type: memory
  type: feedback
  originSessionId: aa46a243-420b-48be-951d-cfa4e7cb9f8b
---

Do NOT edit SchemaTest.lean (or any file the user is actively editing) without first re-reading the latest version from the user's main tree (/local/home/segevem/cedar-spec/). The worktree copy becomes stale whenever the user makes changes. Always `cp` from main tree to worktree BEFORE making edits, not after.

**Why:** The user iterates on SchemaTest.lean between our turns. Copying the worktree version back to the main tree overwrites their changes silently. This has happened multiple times and is very frustrating.

**How to apply:** Before any edit to a file the user may have touched:
1. `cp /local/home/segevem/cedar-spec/<path> /local/home/segevem/cedar-spec/.claude/worktrees/lean-typeof-coverage/<path>`
2. Then make the edit on the worktree copy
3. Then copy back to main tree
