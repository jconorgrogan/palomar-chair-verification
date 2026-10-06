# CLARK figures

## Current opening image

The repository's [opening image](../CLARK_overview.png) is the unchanged supplied `CLARK_level5_slice.png`, renamed for the existing README image path. It is a 2048 × 1152 PNG, with SHA-256 `0115eb0149aa96639d7e6fcc7f5468175dcfd94738757ea248b3a7e6aae11d47`.

It shows a planar section of a level-five CLARK carrier patch with root side 64. The main panel draws carrier sections without individual boundary keys. Both circular insets magnify the same affine plane and resolve the matching bumps and sockets. Their scales relative to the main panel are approximately 11.62494 and 688.88518, rounded in the image to 12× and 690×. The small target ring in the first inset has 2.2 times the radius of the region shown by the deepest inset so that the marker remains visible.

Colours count negative coordinate signs in each stored signed-coordinate frame. The image's “reflected axes” legend refers to those signs, not reflection chirality: every displayed full frame has determinant +1. Heavier lines mark larger carrier supertiles. The dashed line in the deepest inset is the flat carrier-facet reference.

The section plane is `x = C0 + sigma U + tau V`, with

- `U_i = sqrt(2/5) cos(2 pi i/5)`
- `V_i = sqrt(2/5) sin(2 pi i/5)`, for `i = 0, ..., 4`
- `C0 = (40.12787310873329, 40.15101405749027, 40.13330076245207, 40.138820527119655, 40.147602655315815)`

The displayed coordinates are `(tau, -sigma)`. The supplied decimal offset is retained unchanged.

The figure audit found 14,170 intersected unit cells and 3,630 intersected carrier tiles. Independent per-piece and region checks matched the specified carrier sections; the ten intersected key polytopes form five bump/socket pairs whose 17 vertices match exactly in rational world coordinates. Plane clipping and raster comparisons use floating-point arithmetic and small numerical tolerances. This is a numerical rendering of specified geometry, not a symbolic exact-arithmetic rendering proof or an additional Lean verification.

The exact five-dimensional body specification used by the figure audit has SHA-256 `8c94499b8b9fc89efef794497723f649a188de6a7a5460849dc7989bc61b6094`. The [independent tile definition](https://github.com/jconorgrogan/palomar-chair-verification/blob/5f5ceedee770b76c21e8f1105e5e4e3b84b8d676/Challenge.lean) fixes the formal body. The opening PNG is the canonical artwork; no vector-identical version of that PNG is claimed.

## Supplementary diagrams

These PDFs are unchanged copies of the supplied diagrams:

- [Carrier sections](CLARK_sections.pdf): the four midpoint sections contain 8, 8, 8 and 7 unit cubes. All 256 boundary-key solids are disjoint from these sections. SHA-256 `5df4d807e336e3cbca24baf51dcc5a4bdccf8168067644fc0a98d64cccbb74d8`
- [Reference key and matching socket](CLARK_key.pdf): the reference key has half-widths `(1/80, 1/64, 3/160, 7/320)`, apex offsets `(1/240, 1/256, 3/800, 7/1920)` and normal height `1/240`. Panel (h) uses centred facet-chart coordinates. SHA-256 `ba5485c050d7f1850b2cbc9a24836c60466e6f48d198defc077b41a8f31be5c3`

The earlier [carrier-projection PDF](../Clark_5D_tile.pdf) remains as a historical illustration. It is not the current opening image or a PDF version of the current planar section.
