## [Local build](https://help.github.com/en/github/working-with-github-pages/testing-your-github-pages-site-locally-with-jekyll)

0. install Ruby(>=2.4.0)
```
sudo apt-add-repository ppa:brightbox/ruby-ng
sudo apt update
sudo apt install ruby2.4 ruby2.4-dev
echo '# Install Ruby Gems to ~/gems' >> ~/.bashrc
echo 'export GEM_HOME="$HOME/gems"' >> ~/.bashrc
echo 'export PATH="$HOME/gems/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

1. install jekyll and Bundler
```
sudo gem update --system
gem install jekyll bundler
```

2. install dependancies
```
bundle install
```

3. run jekyll site locally
```
bundle exec jekyll serve
# bundle exec jekyll serve --host=0.0.0.0
```

4. visit `http://localhost:4000` (or `http://*.*.*.*:4000`)

### Update gem
```
gem install <gem_name> -v <version>
bundle update
```
