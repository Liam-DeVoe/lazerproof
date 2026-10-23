# lazerproof

Formally verified score processor for osu!(lazer).

tldr: lazer <---fuzz test--> lean model <---prove---> rust processor

We 100% confidence the rust processor is equivalent to the lean model, and very high (but not 100%) confidence the lean model is equivalent to lazer.

Details:

* Lean 4 model of osu!(lazer) score processing, vibed from lazer source code
* Fuzz test Lean model vs osu!(lazer) processor
* Write rust score processor, formally prove equivalent to Lean model

## usage

```
tools/lazerproof https://osu.ppy.sh/scores/<id>
tools/lazerproof <id>
tools/lazerproof replay.osr
```
