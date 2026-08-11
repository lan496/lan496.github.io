# lan496.github.io

Personal page, built with [Jekyll](https://jekyllrb.com/) and the
[minimal-mistakes](https://github.com/mmistakes/minimal-mistakes) theme,
deployed to GitHub Pages by GitHub Actions.

## Local development

Ruby is pinned in `mise.toml`. With [mise](https://mise.jdx.dev/) installed:

```shell
mise trust
mise install
bundle install
```

Then serve the site at `http://localhost:4000`:

```shell
mise run serve
```

Other tasks:

```shell
mise run build   # build into _site/
mise run check   # build, then validate internal links and HTML
```

## Updating dependencies

`Gemfile.lock` is committed so local and CI builds resolve identically.

```shell
bundle update            # all gems
bundle update jekyll     # a single gem
```

The theme is a versioned gem (`minimal-mistakes-jekyll`) rather than a
`remote_theme`, so a theme upgrade is a `Gemfile` bump plus `bundle update`.

## Deployment

`.github/workflows/pages.yml` builds the site on every push and pull request,
runs `htmlproofer` over the output, and deploys to GitHub Pages from `main`.
The repository's Pages source must be set to **GitHub Actions**
(Settings -> Pages -> Build and deployment -> Source).

## License

This repository includes the following software:

- [minimal-mistakes](https://github.com/mmistakes/minimal-mistakes/blob/master/LICENSE)
- [academicons](https://github.com/jpswalsh/academicons)
