# Modern C333 prerequisite sources

This package contains the exact 333 finite prerequisite modules needed by the owned
geometry closure. It excludes the final C theorem. All ordinary source bytes come
from the frozen modern source candidate and are individually locked in the source
manifest; the archive contains regular source files only. No Lean output or
previous build artifact is included.

The migration subset records every additive header/import/public-scope insertion.
Original bodies and explicit private declarations were preserved. No compatibility
option or private-name promotion was introduced. Original source commit:
`c8e274d7833c9e2e1ede5aa61fc042fba8035715`.

The separate reviewed pipeline must compile/check these sources against the exact
official Lean runtime, retain all six modern companions, and admit only same-run
predecessor artifacts. A successful prerequisite build does not establish the final
C theorem, a final geometry theorem, or submission acceptance.
