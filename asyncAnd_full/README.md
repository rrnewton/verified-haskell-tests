
Here we examine a notion of AsyncAnd LVar state which is composed of
two separate boolean IVars plus an (unreachable) error state.

The error state is included to satisfy standard LVar interfaces that
expect a top/error state.

