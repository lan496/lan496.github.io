## [Local build](https://help.github.com/en/github/working-with-github-pages/testing-your-github-pages-site-locally-with-jekyll)

0. Installing Ruby

https://jekyllrb.com/docs/installation/macos/
```shell
/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
brew install ruby@2.7
echo 'export PATH="/usr/local/opt/ruby/bin:/usr/local/lib/ruby/gems/2.7.0/bin:$PATH"' >> ~/.zshrc
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
# bundle add webrick
bundle install
```

3. Running jekyll site locally

```shell
bundle exec jekyll serve
# bundle exec jekyll serve --host=0.0.0.0
```

Now, visit `http://localhost:4000` (or `http://*.*.*.*:4000`).

### Update gem

```
gem install <gem_name> -v <version>
bundle update
```

## References
- [MathJax, Jekyll and github pages - Ben Lansdell](https://benlansdell.github.io/computing/mathjax/)
