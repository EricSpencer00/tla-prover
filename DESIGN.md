# Design System

## Direction

Technical ledger with Swiss research-poster discipline. The page uses a visible column grid, large unromantic typography, compact evidence tables, and an off-register verification red. It is not a magazine and not a terminal.

## Typography

- Display: Archivo Black, 400. Broad, mechanical headings with no faux editorial elegance.
- Body: Atkinson Hyperlegible, 400 and 700. Selected for dense technical reading and character distinction.
- Code and metadata: Recursive Mono, 400 and 600.
- Body measure: 68ch maximum. Headings use fluid `clamp()` sizing and tight line height.

## Color

All colors use OKLCH.

- Paper: `oklch(0.965 0.014 88)`
- Ink: `oklch(0.18 0.018 68)`
- Muted ink: `oklch(0.45 0.025 70)`
- Verification red: `oklch(0.55 0.19 28)`
- Field yellow: `oklch(0.88 0.12 92)`
- Pass green: `oklch(0.49 0.105 151)`

The strategy is committed but restrained: paper and ink dominate, red marks gates and actions, yellow marks active work, and green appears only for verified passes.

## Layout

- Twelve-column desktop grid, four-column mobile grid.
- Full-width evidence rails rather than repeated cards.
- Asymmetric hero: statement occupies eight columns, live gate occupies four.
- Results are table-first. Long explanations sit beside, not above, measurements.
- Spacing follows a 6px base with deliberately varied section rhythm.

## Components

- Gate stamp: square-cornered, text plus state, never color alone.
- Evidence row: metric, numerator/denominator, interpretation, source link.
- Run ledger: chronological table with explicit claim boundary.
- Playground: source editor, action controls, raw structured output, and example reset.
- Source rail: direct links to notebook, plan, ledgers, and reproduction commands.

## Motion

Only functional transitions: navigation underline, disclosure expansion, and result arrival. Use `cubic-bezier(0.16, 1, 0.3, 1)`. Disable nonessential motion under `prefers-reduced-motion`.
