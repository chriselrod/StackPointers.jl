function _precompile_()
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing
    isdefined(StackPointers, Symbol("#1#2")) && precompile(Tuple{getfield(StackPointers, Symbol("#1#2")),Expr})
end
