- before any features, we should refactor this codebase, create own repo and remove unecessary things because these steps add new scripts and stuff, and staying orgniazed is important in scalability of these things.
- Also it is hard to read proofs, which consequently makes proofs harder. like a have should be clear why this have is needed and for what purpose. this may help. 
- seeing cotext at a specific line should be a lot more helpful if they wanna see and trace these things. should be similar to info view. line is optinal not necessary

CLaude suggestion:
```
As for your pipeline refinement idea: the check output is already pretty
  informative, but if you want faster diagnostics, you could have it print
  which specific (by assumption) line number failed AND the full signature
  of the helper being wired â so you can see at a glance which hyp is absent
  without having to cross-reference the .lean file. Does that match what
  you're thinking?
```