module StackPointers

using VectorizationBase
using VectorizationBase: gep

export StackPointer, @def_stackpointer_fallback, @add_stackpointer_method, @def_stackpointer_noalloc, @add_stackpointer_noalloc, stack_pointer_call

struct StackPointer # default to Float64
    ptr::Ptr{Float64}
end
@inline Base.pointer(s::StackPointer) = s.ptr
@inline Base.pointer(s::StackPointer, ::Type{T}) where {T} = Base.unsafe_convert(Ptr{T}, s.ptr)
@inline Base.pointer(s::StackPointer, ::Type{Float64}) = s.ptr
# @inline Base.pointer(s::StackPointer, ::Type{T}) where {T} = reinterpret(Ptr{T}, s.ptr)

@inline Base.convert(::Type{Ptr{T}}, s::StackPointer) where {T} = pointer(s, T)
@inline Base.unsafe_convert(::Type{Ptr{T}}, s::StackPointer) where {T} = pointer(s, T)

# These are for "fuzzing" offsets; answers shouldn't change for SPO ≥ 0, so if they do, there's a bug!
#const SPO = Ref{Int}(800);
#@inline Base.:+(sp::StackPointer, i::Integer) = StackPointer(sp.ptr + i + SPO[])
#@inline Base.:+(i::Integer, sp::StackPointer) = StackPointer(sp.ptr + i + SPO[])

@inline Base.:+(sp::StackPointer, i::Integer) = StackPointer(gep(sp.ptr, i))
@inline Base.:+(sp::StackPointer, i::Integer...) = StackPointer(gep(sp.ptr, +(i...)))
@inline Base.:+(i::Integer, sp::StackPointer) = StackPointer(gep(sp.ptr, i))
@inline Base.:-(sp::StackPointer, i::Integer) = StackPointer(gep(sp.ptr, -i))

VectorizationBase.align(s::StackPointer) = StackPointer(VectorizationBase.align(s.ptr))

# @enum StackPointerSupport::Int8 begin
#     allocate_and_return
#     temporyary_nu
#     None
# end

accepts_stack_pointer(f) = false
returns_stack_pointer(f) = false
function stack_pointer_call(sp::StackPointer, f::F, args...) where {F}
    accepts_stack_pointer(f) ? (returns_stack_pointer(f) ? f(sp, args...) : (sp, f(sp, args...))) : (sp, f(args...))
end


# (Module, function) pairs supported by StackPointer.
#const STACK_POINTER_SUPPORTED_MODMETHODS = Set{Tuple{Symbol,Symbol}}()
const STACK_POINTER_SUPPORTED_METHODS = Set{Symbol}()
const STACK_POINTER_NOALLOC_METHODS = Set{Symbol}()

macro support_stack_pointer(mod, func)
    esc(quote
#        push!(StackPointers.STACK_POINTER_SUPPORTED_MODMETHODS, ($(QuoteNode(mod)),$(QuoteNode(func))))
        push!(StackPointers.STACK_POINTER_SUPPORTED_METHODS, $(QuoteNode(func)))
        @inline $mod.$func(sp::StackPointers.StackPointer, args...) = (sp, $mod.$func(args...))
        StackPointers.accepts_stack_pointer(::typeof($mod.$func)) = true
        StackPointers.returns_stack_pointer(::typeof($mod.$func)) = true
    end)
end
macro support_stack_pointer(func)
    # Could use @__MODULE__
    expr = quote
        push!(StackPointers.STACK_POINTER_SUPPORTED_METHODS, $(QuoteNode(func)))
        @inline $func(sp::StackPointers.StackPointer, args...) = (sp, $func(args...))
        if $func isa Function
            StackPointers.accepts_stack_pointer(::typeof($func)) = true
            StackPointers.returns_stack_pointer(::typeof($func)) = true
        else
            StackPointers.accepts_stack_pointer(::Type{<:$func}) = true
            StackPointers.returns_stack_pointer(::Type{<:$func}) = true
        end
    end
    esc(expr)
end
macro def_stackpointer_fallback(funcs...)
    q = quote end
    for func ∈ funcs
        push!(q.args, :(@inline $func(sp::StackPointers.StackPointer, args...) = (sp, $func(args...))))
        func_defs = quote
            if $func isa Function
                StackPointers.accepts_stack_pointer(::typeof($func)) = true
                StackPointers.returns_stack_pointer(::typeof($func)) = true
            else
                StackPointers.accepts_stack_pointer(::Type{<:$func}) = true
                StackPointers.returns_stack_pointer(::Type{<:$func}) = true
            end
        end
        push!(q.args, func_defs)
    end
    esc(q)
end
macro add_stackpointer_method(funcs...)
    q = quote
        for func ∈ $funcs
            push!(StackPointers.STACK_POINTER_SUPPORTED_METHODS, func)
        end
    end
    esc(q)
end
macro def_stackpointer_noalloc(funcs...)
    q = quote end
    for func ∈ funcs
        push!(q.args, :(@inline $func(sp::StackPointers.StackPointer, args...) = ($func(args...))))
        func_defs = quote
            if $func isa Function
                StackPointers.accepts_stack_pointer(::typeof($func)) = true
            else
                StackPointers.accepts_stack_pointer(::Type{<:$func}) = true
            end
        end
        push!(q.args, func_defs)
    end
    esc(q)
end
macro add_stackpointer_noalloc(funcs...)
    q = quote
        for func ∈ $funcs
            push!(StackPointers.STACK_POINTER_NOALLOC_METHODS, func)
        end
    end
    esc(q)    
end

#function ∂mul end
#function ∂add end
#function ∂muladd end

@support_stack_pointer Base getindex
@support_stack_pointer Base.Broadcast materialize
@support_stack_pointer Base (*)
@support_stack_pointer Base (+)
@support_stack_pointer Base (-)
@support_stack_pointer Base similar
@support_stack_pointer Base copy

#@support_stack_pointer SIMDPirates vmul
#@support_stack_pointer SIMDPirates vadd
#@support_stack_pointer SIMDPirates vsub

#@support_stack_pointer ∂mul
#@support_stack_pointer ∂add
#@support_stack_pointer ∂muladd


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

function __init__()
    _precompile_()
end


end # module
