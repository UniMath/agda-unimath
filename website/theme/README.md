This directory serves as a source of overrides for mdbook's theme. Only the
files which override mdbook's default theme should go here; if you want to add
new support files, put them in the `website` directory in the repo root, and
update `additional-css` and `additional-js` accordingly.

- `index.hbs`
- `head.hbs`
- `header.hbs`
- `css/`
  - `chrome.css`
  - `general.css`
  - `print.css` <- note that we're disabling the `output.html.print` option, so
    a modified version of this file is instead maintained in `website/css`
  - `variables.css`
- `book.js`
- `highlight.js`
- `highlight.css`
- `pagetoc.js`
- `pagetoc.css`
- `catppuccin.css`
- `catppuccin-highlight.css`
- `favicon.svg`
- `favicons.png`
- `fonts/fonts.css`
