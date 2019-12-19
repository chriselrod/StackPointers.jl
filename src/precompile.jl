function _precompile_()
    ccall(:jl_generating_output, Cint, ()) == 1 || return nothing
    isdefined(StackPointers, Symbol("#1#2")) && precompile(Tuple{getfield(StackPointers, Symbol("#1#2")),Expr})
    precompile(Tuple{typeof(Base.setindex_widen_up_to),Array{Symbol,1},StackPointers.StackPointer,Int64})
end
