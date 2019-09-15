using Documenter, StackPointer

makedocs(;
    modules=[StackPointer],
    format=Documenter.HTML(),
    pages=[
        "Home" => "index.md",
    ],
    repo="https://github.com/chriselrod/StackPointer.jl/blob/{commit}{path}#L{line}",
    sitename="StackPointer.jl",
    authors="Chris Elrod <elrodc@gmail.com>",
    assets=String[],
)

deploydocs(;
    repo="github.com/chriselrod/StackPointer.jl",
)
