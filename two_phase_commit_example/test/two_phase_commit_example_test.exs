defmodule TwoPhaseCommitExampleTest do
  use ExUnit.Case
  doctest TwoPhaseCommitExample

  test "greets the world" do
    assert TwoPhaseCommitExample.hello() == :world
  end
end
