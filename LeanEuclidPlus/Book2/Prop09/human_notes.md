- faithfulness checked!

- step 17 took 3.10$ for reference *using opus 4.6*. For cost analysis
1) did the agent really need all those files and why
2) 

- step 18 finished at 4.71$. So this is 1.61$ total.
- step 19 finished at 5.17$. so 0.46$ total.
- step 20 roughly the same. (at 5.60). (roughlyu 0.50$)
- step 21 at 6.06$. so 0.45$

a single node is roughly 0.5$ if easy, 3$ if need to think about structure and have some failures, but can mostly rely on helpers (or previosu steps). Call this medium. Hard ones are those without existing helpers and must derive things from scratch like step 13. Assuming a single file is 0.5$, since step 13 has 10 files, righly 5$ for this step.

Let's say 40% easy, 30% hard, 30% medium. Then for this, since there are 40 steps, we have total cost of this proposition = $0.4*40*0.5+0.3*40*3+0.3*40*5=40*(0.4*0.5+0.3*3+0.3*5)=40*2.6=104\$ $

Using this same thing on proposition 1, since there are 10 steps, it would be roughly $10*2.6=26\$$

This is a **rough** estimate. Prices could be higher or lower. Need to add tracking code and track costs and exact what where and why.

# Actual final cost
From step 18 to the final step (step 39), it costed a total of 18.66$ using opus 4.6. This is 21 steps, so 0.89$ per step. *However*, notice that these later steps are not big *because* they often relied on earlier steps. So this suggests helpers and previous steps, and the "usual" proofs are within reasonable budget, and it is just brand new patterns that should take long.

Also me (human), did *not* need to do *anything* from steps 18 to 39. This was completely automated. I just said /faithful-prove this proposition and it just worked.

# How to reduce costs.
- Assuming $0.5\$$ per simple node is irreducable, the only way to reduce is to minimize files. This can be done through more helpers (we already know this helps), and through actually using them. New proof techinques is hard to reduce costs if never seens before, *but* agent could try and rederive things from scratch and we should track if this happens and how to prevent.

# Important questions
- The helper library. Are we allowed to have this in the "automated" paper presentaitno? The only reason we have these helpers library things is because we ran a few, extracted some manually into helpers, and then kept going. We could say we design manual helpesr to make it easier for the agent and list it as a limitation/cost reduction without being to formal?