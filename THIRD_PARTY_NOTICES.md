# Notices and distribution boundaries

Owned project sources retain their existing Apache-2.0 license and every original
source header. The five audit helpers and normalized physical sources are stored
without edits to their Lean bytes. The source-only packaging adapter is supplied
under the same owned-project license.

The official Lean v4.35.0-rc2 runtime is not bundled. Its release archive hash is
locked, and its LICENSE and LICENSES files must be retained when it is installed.
The unchanged CI helper sources come from pipeline commit
9f7884ebda8fbfd7126fa092f3ccb5d678ec8b98; their hashes are locked.

Pinned Mathlib and companion package sources retain their own licenses and
notices. Their exact Git commits and copied license files are listed in the
external provenance inventory. Widget/node dependencies have additional licenses;
a future source/companion build must retain the notices from its locked dependency
inputs. No npm dependency archive or node_modules object is silently included.
