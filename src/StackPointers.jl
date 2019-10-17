module StackPointers

using VectorizationBase
using MacroTools: @capture, postwalk

export StackPointer, @def_stackpointer_fallback, @add_stackpointer_method, stack_pointer_call

struct StackPointer
    ptr::Ptr{Cvoid}
end
@inline Base.pointer(s::StackPointer) = s.ptr
#@inline Base.pointer(s::StackPointer, ::Type{T}) where {T} = Base.unsafe_convert(Ptr{T}, s.ptr)
@inline Base.pointer(s::StackPointer, ::Type{T}) where {T} = reinterpret(Ptr{T}, s.ptr)

@inline Base.convert(::Type{Ptr{T}}, s::StackPointer) where {T} = pointer(s, T)
@inline Base.unsafe_convert(::Type{Ptr{T}}, s::StackPointer) where {T} = pointer(s, T)

# These are for "fuzzing" offsets; answers shouldn't change for SPO ≥ 0, so if they do, there's a bug!
#const SPO = Ref{Int}(800);
#@inline Base.:+(sp::StackPointer, i::Integer) = StackPointer(sp.ptr + i + SPO[])
#@inline Base.:+(i::Integer, sp::StackPointer) = StackPointer(sp.ptr + i + SPO[])

@inline Base.:+(sp::StackPointer, i::Integer...) = StackPointer(+(sp.ptr, i...))
@inline Base.:+(i::Integer, sp::StackPointer) = StackPointer(sp.ptr + i)
@inline Base.:-(sp::StackPointer, i::Integer...) = StackPointer(-(sp.ptr, i...))

VectorizationBase.align(s::StackPointer) = StackPointer(VectorizationBase.align(s.ptr))

supports_stack_pointer(f) = false
function stack_pointer_call(sp::StackPointer, f::F, args...) where {F}
    supports_stack_pointer(f) ? f(sp, args...) : (sp, f(args...))
end


# (Module, function) pairs supported by StackPointer.
#const STACK_POINTER_SUPPORTED_MODMETHODS = Set{Tuple{Symbol,Symbol}}()
const STACK_POINTER_SUPPORTED_METHODS = Set{Symbol}()

macro support_stack_pointer(mod, func)
    esc(quote
#        push!(StackPointers.STACK_POINTER_SUPPORTED_MODMETHODS, ($(QuoteNode(mod)),$(QuoteNode(func))))
        push!(StackPointers.STACK_POINTER_SUPPORTED_METHODS, $(QuoteNode(func)))
        @inline $mod.$func(sp::StackPointers.StackPointer, args...) = (sp, $mod.$func(args...))
        StackPointers.supports_stack_pointer(::typeof($mod.$func)) = true
    end)
end
macro support_stack_pointer(func)
    # Could use @__MODULE__
    esc(quote
#        push!(StackPointers.STACK_POINTER_SUPPORTED_MODMETHODS, ($(QuoteNode(mod)),$(QuoteNode(func))))
        push!(StackPointers.STACK_POINTER_SUPPORTED_METHODS, $(QuoteNode(func)))
        @inline $func(sp::StackPointers.StackPointer, args...) = (sp, $func(args...))
        if $func isa Function
        StackPointers.supports_stack_pointer(::typeof($func)) = true
        else
        StackPointers.supports_stack_pointer(::Type{<:$func}) = true
        end
    end)
end
macro def_stackpointer_fallback(funcs...)
    q = quote end
    for func ∈ funcs
        push!(q.args, :(@inline $func(sp::StackPointers.StackPointer, args...) = (sp, $func(args...))))
        push!(q.args, quote
              if $func isa Function
              StackPointers.supports_stack_pointer(::typeof($func)) = true
              else
              StackPointers.supports_stack_pointer(::Type{<:$func}) = true
              end
              end)
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



function stack_pointer_pass(expr, stacksym, blacklist = nothing, verbose::Bool = false, m = :StackPointers)
    if blacklist == nothing
        whitelist = STACK_POINTER_SUPPORTED_METHODS
    else
        whitelist = setdiff(STACK_POINTER_SUPPORTED_METHODS, blacklist)
    end
#    verbose = true
    postwalk(expr) do ex
        if @capture(ex, B_ = mod_.func_(args__)) && func ∈ whitelist
            if verbose
                str = "Args: $args; output: $B"
                q = quote
                    println($(string(func)))
                    println($str)
                end
                for arg in args
                    push!(q.args, :(@show $arg))
                end
                push!(q.args, :(@show typeof.($(Expr(:tuple,args...)))))
                push!(q.args, :(($stacksym, $B) = $mod.$func($stacksym::($m.StackPointer), $(args...))))
                push!(q.args, :(@show divrem(reinterpret(Int, pointer($stacksym)), $(VectorizationBase.REGISTER_SIZE))))
                push!(q.args, :(println("Result: ")))
                push!(q.args, :(@show $B))
                return q
            else
                return :(($stacksym, $B) = $mod.$func($stacksym, $(args...)))
            end
        elseif @capture(ex, B_ = func_(args__)) && func ∈ whitelist
            ##            if func ∈ whitelist
            if verbose
                str = "Args: $args; output: $B"
                q = quote
                    println($(string(func)))
                    println($str)
                end
                for arg in args
                    push!(q.args, :(@show $arg))
                end
                push!(q.args, :(@show typeof.($(Expr(:tuple,args...)))))
                push!(q.args, :(($stacksym, $B) = $func($stacksym::($m.StackPointer), $(args...))))
                push!(q.args, :(@show divrem(reinterpret(Int, pointer($stacksym)), $(VectorizationBase.REGISTER_SIZE))))
                push!(q.args, :(println("Result: ")))
                push!(q.args, :(@show $B))
                return q
            else
                return :(($stacksym, $B) = $func($stacksym, $(args...)))
            end
##            elseif func isa GlobalRef && func.name ∈ whitelist
##                return :(($stacksym, $B) = $(func.name)($stacksym, $(args...)))
##            end
        elseif @capture(ex, B_ = mod_.func_{T__}(args__)) && func ∈ whitelist
            if verbose
                str = "Args: $args; output: $B"
                q = quote
                    println($(string(func)))
                    println($str)
                end
                for arg in args
                    push!(q.args, :(@show $arg))
                end
                push!(q.args, :(@show typeof.($(Expr(:tuple,args...)))))
                push!(q.args, :(($stacksym, $B) = $mod.$func{$(T...)}($stacksym::($m.StackPointer), $(args...))))
                push!(q.args, :(@show divrem(reinterpret(Int, pointer($stacksym)), $(VectorizationBase.REGISTER_SIZE))))
                push!(q.args, :(println("Result: ")))
                push!(q.args, :(@show $B))
                return q
            else
                return :(($stacksym, $B) = $mod.$func{$(T...)}($stacksym, $(args...)))
            end
        elseif @capture(ex, B_ = func_{T__}(args__)) && func ∈ whitelist
            if verbose
                str = "Args: $args; output: $B"
                q = quote
                    println($(string(func)))
                    println($str)
                end
                for arg in args
                    push!(q.args, :(@show $arg))
                end
                push!(q.args, :(@show typeof.($(Expr(:tuple,args...)))))
                push!(q.args, :(($stacksym, $B) = $func{$(T...)}($stacksym::($m.StackPointer), $(args...))))
                push!(q.args, :(@show divrem(reinterpret(Int, pointer($stacksym)), $(VectorizationBase.REGISTER_SIZE))))
                push!(q.args, :(println("Result: ")))
                push!(q.args, :(@show $B))
                return q
            else
                return :(($stacksym, $B) = $func{$(T...)}($stacksym, $(args...)))
            end
        else
            return ex
        end
    end
end


end # module
