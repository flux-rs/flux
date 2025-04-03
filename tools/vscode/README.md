# flux-dev

VS Code extension with language support for flux rust intermediate representations

## Install

**Step 1.** To get the extension running you need to **build** the `vsix` file and **install** it manually

```bash
$ npm install -g typescript
$ npm install -g vsce
$ vsce package
```

**Step 2.** Install `flux`

Following [these instructions](https://flux-rs.github.io/flux/guide/install.html)

**Step 3.** Run the extension!

You can then **enable** the extension by runnning the `Toggle Flux View` command in the command palette.

## Features

Syntax Highlighting

- For `flux` type signatures
- For `flux` constraints (generated with `FLUX_DUMP_CONSTRAINT=1` for debugging)

Flux View Panel: shows the types and environments known at each program point

- If your cursor is _at or before_ the first non-blank character of a line, the panel will show the types and environments _before_ that line
- Else the panel will show the types and environments _after_ that line

![Before Statement](static/flux_view_start.jpg)

![After Statement](static/flux_view_end.jpg)