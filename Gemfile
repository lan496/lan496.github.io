source "https://rubygems.org"

gem "jekyll", "~> 4.4"
gem "minimal-mistakes-jekyll", "~> 4.28"

group :jekyll_plugins do
  gem "jekyll-feed", "~> 0.17"
  gem "jekyll-gist", "~> 1.5"
  gem "jekyll-include-cache", "~> 0.2"
  gem "jekyll-seo-tag", "~> 2.8"
  gem "jekyll-sitemap", "~> 1.4"
end

gem "kramdown-parser-gfm", "~> 1.1"
gem "webrick", "~> 1.9"

# Octokit (via jekyll-gist) needs this for retry support on Faraday 2.
gem "faraday-retry", "~> 2.3"

group :development, :test do
  gem "html-proofer", "~> 5.0"
end

# Unbundled from the Ruby standard library in 3.4; required by Jekyll's deps.
gem "base64", "~> 0.2"
gem "bigdecimal", "~> 3.1"
gem "csv", "~> 3.3"
gem "logger", "~> 1.6"
