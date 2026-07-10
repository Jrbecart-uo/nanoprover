"""
Entry point: wire a kernel to a portfolio of intuition agents and search.

Two modes:
  --mock                 run the offline MockEnv (no Lean, no API key) so you can
                         see the whole loop work today.
  (default)              LeanDojoEnv against a real mathlib theorem; requires the
                         toolchain from README.md and ANTHROPIC_API_KEY.

Examples:
  python run.py --mock
  python run.py --mock --no-claude          # portfolio = builtins only
  python run.py --repo <url> --commit <sha> --file <path.lean> --theorem <fqn>
"""

import argparse
import sys

from proof_env import MockEnv, LeanDojoEnv
from agents import (BuiltinAgent, ClaudeAgent, DeepSeekProverAgent,
                    PortfolioAgent, MockRewriteAgent)
from search import search


def build_agent(use_claude: bool, use_deepseek: bool, model: str):
    sources = [BuiltinAgent()]
    if use_claude:
        try:
            sources.append(ClaudeAgent(model=model))
        except Exception as e:
            print("!! Claude agent unavailable ({}); continuing without it.".format(e))
    if use_deepseek:
        sources.append(DeepSeekProverAgent())
    print("Portfolio: {}".format(", ".join(a.name for a in sources)))
    return PortfolioAgent(sources)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--mock", action="store_true",
                    help="use the offline MockEnv instead of Lean")
    ap.add_argument("--no-claude", action="store_true",
                    help="drop Claude from the portfolio (builtins only)")
    ap.add_argument("--deepseek", action="store_true",
                    help="add the DeepSeek-Prover stub to the portfolio")
    ap.add_argument("--model", default="claude-opus-4-8",
                    help="Claude model id (default: %(default)s; "
                         "use claude-fable-5 for the hardest goals)")
    # Lean target (ignored in --mock):
    ap.add_argument("--repo", default="https://github.com/leanprover-community/mathlib4")
    ap.add_argument("--commit", default=None)
    ap.add_argument("--file", default=None)
    ap.add_argument("--theorem", default=None)
    ap.add_argument("--branching", type=int, default=8)
    ap.add_argument("--max-expansions", type=int, default=200)
    args = ap.parse_args(argv)

    agent = build_agent(use_claude=not args.no_claude,
                        use_deepseek=args.deepseek, model=args.model)

    if args.mock:
        env = MockEnv()
        print("MockEnv goal: {!r}  ->  target 'SUM'".format(env.initial_state().pp))
        print("(available rewrite rules: {})".format(env.rules()))
        # The mock kernel speaks rewrites, not Lean tactics -- use the offline
        # oracle as the intuition engine so the demo is self-contained.
        mock_agent = PortfolioAgent([MockRewriteAgent(env.rules())])
        with env:
            result = search(env, mock_agent, branching=args.branching,
                            max_expansions=args.max_expansions)
    else:
        missing = [n for n, v in (("--commit", args.commit), ("--file", args.file),
                                  ("--theorem", args.theorem)) if not v]
        if missing:
            ap.error("Lean mode requires {} (or pass --mock)".format(", ".join(missing)))
        with LeanDojoEnv(args.repo, args.commit, args.file, args.theorem) as env:
            print("Proving {} in {}".format(args.theorem, args.file))
            print("Initial goal:\n{}".format(env.initial_state().pp))
            result = search(env, agent, branching=args.branching,
                            max_expansions=args.max_expansions)

    return 0 if result.solved else 1


if __name__ == "__main__":
    sys.exit(main())
