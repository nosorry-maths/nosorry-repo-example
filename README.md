# nosorry-repo-example

A minimal **repository submission** for [nosorry](https://nosorry.tail520a1c.ts.net): the verified proof of
Written on the Wall II, Conjecture 96, as a Lake project of two modules.

- `lakefile.toml` (declarative; a `lakefile.lean` is refused) requiring formal-conjectures, pinned in `lake-manifest.json`
- `NosorryExample/Main.lean` holds the theorem `WrittenOnTheWallII.GraphConjecture96.conjecture96` with the exact statement; it imports `NosorryExample/Extra.lean`

Submit with: `nosorry submit <slug> --repo-url https://github.com/nosorry-maths/nosorry-repo-example --commit <sha> --module NosorryExample.Main`
