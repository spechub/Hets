import hs.Prelude
from hs.Hets.Python import *
from hs.Driver.Options import defaultHetcatsOpts
from hs.Data.Maybe import fromJust
from hs.Common.Result import resultToMaybe



result = loadLibrary("Family.dol", defaultHetcatsOpts).act()
nameAndEnv = fromJust(resultToMaybe(result))
name = hs.Prelude.fst(nameAndEnv)
env = hs.Prelude.snd(nameAndEnv)

graph = getGraphForLibrary(name, env)
[family1, family2] = getNodesFromDevelopmentGraph(graph)

th1 = getTheoryFromNode(family1)
th2 = getTheoryFromNode(family2)

provers = list(usableProvers(th1).act())
pellet = provers[0]

prover = hs.Prelude.Just(hs.Prelude.fst(pellet))
comorphism = hs.Prelude.Just(hs.Prelude.snd(pellet))

proof1 = autoProveNode(th1, prover, comorphism).act()
proof2 = autoProveNode(th2, prover, comorphism).act()