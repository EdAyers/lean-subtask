import .data
namespace robot


meta def task.test : task → expr → M bool := notimpl
meta def task.refine : task → M E := notimpl

meta def strategy.execute : strategy → expr → tactic rule := notimpl


end robot