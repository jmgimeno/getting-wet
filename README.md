# getting-wet

Playground for LiquidHaskell.

## Notes to myself

* Changing to homebrew's z3@4.8.8

  ```shell_session
  $ brew unlink z3
  $ cd /usr/local/Homebrew/Library/Taps/homebrew/homebrew-core/Formula
  $ git log --follow z3.rb
  $ git checkout -b z3-4.8.8 9591758
  $ brew reinstall ./z3.rb
  $ brew switch z3 4.8.8
  $ git checkout master
  ```
