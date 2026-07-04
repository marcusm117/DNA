# On july 3 1pm before any claude max, the status for book 1 is:
- props 1 to 10 inclusive are all mapped
- props 1 to 3 are all completely done (personal glm account)
- finished at 3:50 roughly.


# On date xx, finished props ..., and the weekly statuis is I% used.
- roughly x% weekly status for N props.

# proof costs (according to /status):
## Using sonnet
### Prop 4
```
 Session

  Total cost:            $17.17
  Total duration (API):  1h 32m 12s
  Total duration (wall): 2h 27m 49s
  Total code changes:    336 lines added, 78 lines removed
  Usage by model:
     claude-sonnet-4-6:  8.6k input, 326.1k output, 29.2m cache read, 933.6k cache write ($17.17)
      claude-haiku-4-5:  453 input, 13 output, 0 cache read, 0 cache write ($0.0005)

``` 
### Prop 5
```

  Total cost:            $15.16
  Total duration (API):  1h 15m 37s
  Total duration (wall): 2h 17m 44s
  Total code changes:    536 lines added, 82 lines removed
  Usage by model:
     claude-sonnet-4-6:  5.9k input, 284.3k output, 29.1m cache read, 571.5k cache write ($15.16)
```
### Prop 7
```
  Settings  Status   Config   Usage   Stats

  Session

  Total cost:            $12.04
  Total duration (API):  1h 21m 41s
  Total duration (wall): 2h 20m 13s
  Total code changes:    282 lines added, 98 lines removed
  Usage by model:
     claude-sonnet-4-6:  4.1k input, 288.1k output, 19.3m cache read, 509.8k cache write ($12.04)
      claude-haiku-4-5:  441 input, 13 output, 0 cache read, 0 cache write ($0.0005)
```

# split and map costs (according to /status):
## Using sonnet
### Prop 11
```
  Total cost:            $1.55
  Total duration (API):  12m 55s
  Total duration (wall): 2h 35m 17s
  Total code changes:    143 lines added, 15 lines removed
  Usage by model:
     claude-sonnet-4-6:  712 input, 51.1k output, 1.5m cache read, 84.9k cache write ($1.55)
      claude-haiku-4-5:  440 input, 13 output, 0 cache read, 0 cache write ($0.0005)

```
### Prop 13
```
  Total cost:            $2.47
  Total duration (API):  20m 42s
  Total duration (wall): 1h 53m 25s
  Total code changes:    195 lines added, 56 lines removed
  Usage by model:
     claude-sonnet-4-6:  1.1k input, 78.5k output, 2.9m cache read, 115.9k cache write ($2.47)
      claude-haiku-4-5:  642 input, 17 output, 0 cache read, 0 cache write ($0.0007)

```
### Prop 12
ran into a wts issue.

# Takeaways
1. Sonnet is sufficient for the 3 proofs and the 3 maps I've tried, so I will be using this unless I encouter issues
2. A proposition is proved in 2-3 hours wall time. A complete proposition for prooving takes slightly less than 1/3 of the total usage limit for this session.
3. At this rate, we can do two sessions a day hopefully. 6 props a day, to get the remaining 48-8=40, would require 7 days. a week and we are done if we do 6 a day. So roughly two weeks to finish book 1 and also book 3 perhaps at this rate? though problems likely will occur so I would say this is best case
4. If we had unlimited budget, at this rate of doing 3 maps, and 3 proofs parallel (this is comfortable for me to monitor and make sure agent does not go off track), it is roughly 3 done within at most 3 hours. In a day, I could spend 9 hours on it, and get 9 done in a day, though I would expect slightly more once I am more comfortable with tihs workflow. So let's say 10 a day. 4 days and I am done Book 1, 3 days I am done Book 3 in best case scenario.
5. For actual budget costs, an upper bound for the average we have so far seen is roughly 3$ for mapping, 20$ for proving, and let's say 5$ extra for unexpected problems. So roughly 30$ per prop, and this totals up to be for the 30 remainign 900$.
6. The cost spent yesterecay and stuff like that was mostly on setup, fixing lots of small issues (eg. stray spaces in sentences, assumptions always being there, trying out the tui and running small scale only to realize tihs is not a good idea since I cannot interact with agent directly and agent often times does dumb things so better to monitor).



# My personal Notes

# aside. copy paste text to proofs:
/faithful-prove /LeanEuclidPlus/Book1/Prop15. Please note that the same nearly identical proof exists at Book/ just this one is more faithful so you SHOULD use that existing one to help you prove things and no reinvent the patterns if you ever struggle with something. Note you are in DNA and must cd to LeanEuclidPlus.

# map copy paste

/faithful-split /LeanEuclidPlus/Book1/Prop18. Note you are in DNA and must cd to LeanEuclidPlus.

/faithful-map /LeanEuclidPlus/Book1/Prop07. Please note that the same nearly identical proof exists at Book/ just this one is more faithful so you SHOULD reference this.

# path
/u/taddmao/code/autoform/DNA/
- start time 1:20pm June 3rd.
- session limit hit at 3: