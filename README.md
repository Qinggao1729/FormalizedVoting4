# Formalized-Voting-4

Lean 4.21.0 + Mathlib4 port of [Chase Norman's Formalized Voting in Lean 3](https://github.com/chasenorman/Formalized-Voting).

The version of mathlib3 he used is in [here](https://github.com/leanprover-community/mathlib3/blob/2ecd65e6de2939f09df9d964782f8ec7ba4aeb5c).

Key changes:
- Uses Mathlib4 names/imports/tactics.
- Remove some lemmas in Lean3 code in case they are defined in Mathlib4.
- Replaces Lean3 `stream` by Lean4 `Stream' X`.
- `List`: For list indexing, Mathlib4 `List` uses both `get ⟨i, hle⟩` and `getElem` (notation `[]`, which is a tactic), whereas Mathlib3 `list` only uses `nth_le i hle`. For chain-cheking, Mathlib4 uses `IsChain R l` whereas Mathlib3 uses `chain R a l`.


## Installation instructions
I recommend installing Lean4 from VSCode exensions, as mentioned in https://lean-lang.org/install/.

Download this project by running `git clone`. Then in VSCode, click Lean4 menu -> Open project -> Open local project.


## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
