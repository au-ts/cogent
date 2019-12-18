Contributions to the Cogent repository are welcome!

To keep the license rights for this projects clear, we require a Contributor
Licence Agreement (CLA) for all contributions.

The Licence agreement certifies:
  * That you have the rights to give us the contribution, and
  * That you give us the rights to use your contribution

Please sign the [Contributor License Agreement](http://ssrg.nicta.com.au/projects/TS/cogent.pml#contrib), scan it and send it to us at
*cla AT trustworthy.systems*

For this repository, we can review pull requests directly on github if we have a
signed CLA on file, no need to email a patch.

If you have only small trivial changes such as style, typos, comments, or white
space and don't want to sign a CLA for that, please file an issue in the github
issue tracker, we'll usually be happy to do the change for you and attribute
your idea by linking to the github issue in the change set comment.


Git conventions:
* Commit subject line starts with a short tag, indicating the area of the work. E.g.
  `compiler`, `doc`, `c-refinement`, `ci`, `bilby`. These are not predefined; you can
  make up new ones as long as they make sense.
* Refer to the relevant GitHub tickets, if any.
* Use a `[skip ci]` tag (see: https://docs.travis-ci.com/user/customizing-the-build/#skipping-a-build)
  in the body of the commit message (not in the subject line), if your changes don't
  require the Travis regression test.
* Use a `[skip lemma]` tag in the body of the commit message, if your changes don't involve
  Isabelle/HOL specifications and proofs.
* Don't worry if you are unsure what to put. We'll amend the messages accordingly when we
  "merge" pull requests.
* Don't `merge`. We prefer a linear history with `git rebase`.
