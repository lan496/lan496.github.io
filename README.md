## [Local build](https://help.github.com/en/github/working-with-github-pages/testing-your-github-pages-site-locally-with-jekyll)

0. Installing Ruby

```shell
brew install rbenv ruby-build
rbenv install 3.2.2
rbenv global 3.2.2
echo $SHELL
which ruby
ruby -v
```

1. Installing Bundler and jekyll

```shell
gem update --system
gem install --user-install bundler jekyll
```

2. Installing dependencies

```shell
bundle install
```

3. Running jekyll site locally

```shell
bundle exec jekyll serve --livereload
# bundle exec jekyll serve --livereload --host=0.0.0.0
```

Now, visit `http://localhost:4000` (or `http://*.*.*.*:4000`).

### Update gem

```
gem install <gem_name> -v <version>
bundle update
```

## References
- [MathJax, Jekyll and github pages - Ben Lansdell](https://benlansdell.github.io/computing/mathjax/)

## License

This repository includes the following softwares
- [minimal-mistakes](https://github.com/mmistakes/minimal-mistakes/blob/master/LICENSE)
- [academicons](https://github.com/jpswalsh/academicons)
