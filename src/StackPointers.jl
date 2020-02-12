module StackPointers

using VectorizationBase
using VectorizationBase: gep

export StackPointer, stack_pointer_call

struct StackPointer # default to Float64
    ptr::Ptr{Float64}
end
@inline Base.pointer(s::StackPointer) = s.ptr
@inline Base.pointer(s::StackPointer, ::Type{T}) where {T} = Base.unsafe_convert(Ptr{T}, s.ptr)
@inline Base.pointer(s::StackPointer, ::Type{Float64}) = s.ptr

@inline Base.convert(::Type{Ptr{T}}, s::StackPointer) where {T} = pointer(s, T)
@inline Base.unsafe_convert(::Type{Ptr{T}}, s::StackPointer) where {T} = pointer(s, T)

@inline Base.:+(sp::StackPointer, i::Integer) = StackPointer(gep(sp.ptr, i))
@inline Base.:+(sp::StackPointer, i::Integer...) = StackPointer(gep(sp.ptr, +(i...)))
@inline Base.:+(i::Integer, sp::StackPointer) = StackPointer(gep(sp.ptr, i))
@inline Base.:-(sp::StackPointer, i::Integer) = StackPointer(gep(sp.ptr, -i))

@inline VectorizationBase.align(s::StackPointer) = StackPointer(VectorizationBase.align(s.ptr))


"""
To support using StackPointers, overload stack_pointer_call.
For example, in PaddedMatrices (which defines an appropriate `similar` method):

@inline function StackPointers.stack_pointer_call(::typeof(*), sp::StackPointer, A::AbstractMatrix, B::AbstractVecOrMat)
    (sp, C) = similar(sp, A, B)
    sp, mul!(C, A, B)
end

"""
@inline stack_pointer_call(f::F, sp::StackPointer, args...) where {F} = (sp, f(args...))


function extract_func_sym(f::Expr)::Symbol
    if f.head === :(.)
        f.args[2].value
    elseif f.head === :curly
        ff = first(f.args)
        ff isa Symbol ? ff : ff.args[2].value
    end
end

function stack_pointer_pass!(expr, stacksym, blacklist = nothing, verbose::Bool = false, m = :StackPointers)
    whitelist = union(STACK_POINTER_NOALLOC_METHODS, STACK_POINTER_SUPPORTED_METHODS)
    if blacklist == nothing
        whitelist = whitelist
    else
        whitelist = setdiff(whitelist, blacklist)
    end
    for (i,ex) ∈ enumerate(expr.args)
        ex isa Expr || continue
        if ex.head === :block
            stack_pointer_pass!(ex, stacksym, blacklist, verbose, m)
            continue
        end
        ex.head === :(=) || continue
        B = ex.args[1]
        RHS = ex.args[2]
        (RHS isa Expr && RHS.head === :call) || continue
        f = first(RHS.args)
        func::Symbol = f isa Symbol ? f : extract_func_sym(f)
        func ∈ whitelist || continue
        ret = func ∈ STACK_POINTER_NOALLOC_METHODS ? B : Expr(:tuple, stacksym, B)
        fcall = Expr(:call, f, stacksym)
        append!(fcall.args, @view(RHS.args[2:end]))
        retexpr = Expr(:(=), ret, fcall)
        expr.args[i] = retexpr
        verbose || continue
        str = "Args: $args; output: $B"
        q = quote
            println($(string(func)))
            println($str)
        end
        for arg in args
            push!(q.args, :(@show $arg))
        end
        push!(q.args, :(@show typeof.($(Expr(:tuple,args...)))))
        push!(q.args, retexpr)#:($ret = $f($stacksym::($m.StackPointer), $(args...))))
        push!(q.args, :(@show divrem(reinterpret(Int, pointer($stacksym)), $(VectorizationBase.REGISTER_SIZE))))
        push!(q.args, :(println("Result: ")))
        push!(q.args, :(@show $B))
        expr.args[i] = q
    end
end

include("precompile.jl")
_precompile_()

end # module
