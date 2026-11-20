# How is peak calculated?

## Principles

- At each point on an allowed execution, add the modeled bytes live together. The contract must cover the greatest such total on every allowed execution.
- A check of current memory can fall after a drop. A check of peak memory still includes the earlier high point.

## Specific rules

- [Branches and loops](branches-and-loops.md)
- [Calls and sections](calls-and-sections.md)
