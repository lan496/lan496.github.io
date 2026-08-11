# CLAUDE.md

Personal academic site for Kohei Shinohara, served at https://lan496.github.io.
Jekyll 4.4 with the `minimal-mistakes-jekyll` gem theme, deployed to GitHub
Pages by GitHub Actions.

## Always run Ruby through mise

Ruby 3.4.10 is pinned in `mise.toml`. macOS system Ruby is 2.6.10 and the old
rbenv 3.2.2 install is broken (it resolves `libgmp.10.dylib` against a stale
pyenv path), so a bare `bundle` may silently pick the wrong interpreter:

```shell
mise exec -- bundle exec jekyll build
```

Tasks wrap the common cases:

```shell
mise run serve   # localhost:4000 with live reload
mise run build   # build into _site/
mise run check   # build, then htmlproofer over the output
```

Run `mise trust` once after cloning. `mise trust` and `bundle install` write
outside the repo and to the network, so both need the sandbox disabled.

## Where things live

- `_pages/*.md` -- every page, each with an explicit `permalink`. There is no
  blog index; `_config.yml` sets page defaults (single layout, sticky TOC).
- `_data/navigation.yml` -- masthead links. A new page needs an entry here.
- `_config.yml` -- theme is set via `theme:`, not `remote_theme:`.
- `_includes/head/custom.html` -- only pulls in academicons.
- `assets/css/main.scss` -- 15 lines on top of the theme; not a fork.
- `notes/` and `assets/poster/` -- PDFs, committed directly.

## Gotchas

**`_posts/` files need a `YYYY-MM-DD-` filename prefix.** Without it Jekyll
skips them silently. `primitive_cell_search.md` and `unique_shifts.md` have no
prefix and have never been published.

**There is no MathJax.** `use_math: true` in front matter does nothing; the old
wiring was removed as dead code. Adding math means wiring MathJax 3 into
`_includes/head/custom.html` first.

**Root-level files leak into `_site/` unless excluded.** `mise.toml` and
`Gemfile.lock` are in the `exclude:` list in `_config.yml`. Add new root files
there too.

**`/notes/` is both a page and a static directory.** `_pages/notes.md` renders
to `_site/notes/index.html` alongside the copied PDFs. Links from that page are
relative to `/notes/`.

**`publications.md` numbers every list item `1.`** and relies on Markdown
auto-numbering. Do not renumber them, and do not run a Markdown formatter over
the file.

**htmlproofer enforces HTTPS**, so new links must be `https://`. It runs with
`--disable-external`, meaning dead external hosts are not caught -- one such
link (`www-erato.ist.hokudai.ac.jp`, NXDOMAIN) is kept deliberately as a
historical citation.

**Sass deprecations are silenced on purpose** via `quiet_deps` and
`silence_deprecations` in `_config.yml`. The theme vendors Susy and is
`@import`-based upstream, so `main.scss` cannot move to `@use` yet. A clean
build should emit zero warnings; if warnings appear, something else regressed.

## Dependencies

`Gemfile.lock` is committed so local and CI builds resolve identically. It must
keep the `x86_64-linux` platform or CI cannot install, and `BUNDLED WITH` is
pinned to 2.6.9 (Ruby 3.4.10's default) to avoid pulling the unvalidated
bundler 4 major:

```shell
mise exec -- bundle update
mise exec -- bundle lock --add-platform x86_64-linux   # if platforms are lost
```

The theme is a versioned gem, so upgrading it is a `Gemfile` bump plus
`bundle update`, not a `remote_theme` string change.

## Deployment

`.github/workflows/pages.yml` builds on every push and pull request, runs
htmlproofer, and deploys from `main` only. The repository's Pages source must
be **GitHub Actions** (Settings -> Pages), not deploy-from-branch. The build job
deliberately omits `actions/configure-pages`: this is a user site at the domain
root, so `baseurl` is empty and the build should not depend on the Pages
setting.
