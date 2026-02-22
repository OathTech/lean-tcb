/- Copyright (c) 2026 Mike Dodds. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Dodds -/

import LeanTcb.Types
import LeanTcb.Classify
import LeanTcb.Core
import LeanTcb.Attr
import LeanTcb.Format
import LeanTcb.Command

/-!
# LeanTcb: Trust Boundary Classifier

A Lean 4 meta-tool that classifies every declaration reachable from
an entry-point theorem as either specification (must be human-reviewed)
or proof infrastructure (kernel-verified).

## Usage

```lean
import LeanTcb

#tcb myMainTheorem
#tcb! myThm1 myThm2  -- verbose: includes library dependencies
```

## Main definitions

- `LeanTcb.computeTcb`: the core worklist traversal
- `LeanTcb.tcbAttr`: the `@[tcb]` annotation attribute
- `LeanTcb.formatResult`: output categorization
- `LeanTcb.renderResult`: infoview rendering
-/
