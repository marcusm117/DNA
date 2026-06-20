# Priority

- Do number 10 first. THe main reason is tracking, and never needing to look back. We can check each step one at a time, and only things in the @deps. Ideally @deps is not listing everything but we do not enforce it I guess. this is more of a readability and tracking thing.
- #1 very imoprtant. this is the foundation of lots of the ideas. basically a smart grep tool
- #9 seems very useful for speeding things up as a search tool. Wondering if we should allow some specific grep tooling since agents like spamming grep.
- yes # 3 is useful and related to #9
- #4 is also very useful to make it like "this should work" tool, though maybe not that necessary if ai is smart, which it should be


# maybe don't do
- #11 is not important rn. it is more of a cleanup tool, and rn we are just trying to get proofs working.
- #6 is also just cleanup, and very related to @deps? maybe these things it reports must actually be an issue?
- #2 seems not a good idea. if ai is relying on this, it is too dumb, and will believe timeout means true. a smart ai should manually check. ai needs to be smart enough to realize if something is true or not. trace should be done in their head of why it is true written in NL first. it should not be relying on a code smell thing. if code smell caches, the ai MUST be smart enough to have realized the outcome before sm or the ai is too stupid is my thought process.


# questions
- #7 what even does this mean? this is literally #3 no?
- #5 I think the 45s thing already fixes it?