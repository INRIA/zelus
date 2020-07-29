from pyzls import CNode
import numpy as np


class Prob:
    def __init__(self, idx: int, scores):
        self.idx = idx
        self.scores = scores


class sample(CNode):
    def __init__(self):
        pass

    def reset(self):
        pass

    def copy(self, dest):
        pass

    def step(self, prob: Prob, dist):
        return dist.sample()


class observe(CNode):
    def __init__(self):
        pass

    def reset(self):
        pass

    def copy(self, dest):
        pass

    def step(self, prob: Prob, dist, obs):
        prob.scores[prob.idx] += dist.log_prob(obs)
        return ()


def infer(n: int):
    def infer(f: CNode):
        class infer(CNode):
            def __init__(self):
                self.scores = np.zeros(n)
                self.particles = np.array([f() for _ in range(n)])

            def reset(self):
                self.scores.fill(0)
                for p in self.particles:
                    p.reset()

            def copy(self, dest):
                pass

            def step(self, *args):
                values = np.array(
                    [
                        p.step(Prob(i, self.scores), *args)
                        for i, p in enumerate(self.particles)
                    ]
                )
                probs = np.exp(self.scores)
                probs = probs / np.sum(probs)
                ids = np.random.choice(n, size=n, p=probs)
                particles = [f() for _ in range(n)]
                for i, idx in enumerate(ids):
                    self.particles[idx].copy(particles[i])
                self.particles = np.array(particles)
                self.scores.fill(0)
                return values[ids]

        return infer

    return infer
