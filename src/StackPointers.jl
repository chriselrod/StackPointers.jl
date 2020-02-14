module StackPointers

using VectorizationBase

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

# function extract_func_sym(f::Expr)::Symbol
#     if f.head === :(.)
#         f.args[2].value
#     elseif f.head === :curly
#         ff = first(f.args)
#         ff isa Symbol ? ff : ff.args[2].value
#     end
# end

include("precompile.jl")
_precompile_()

end # module
