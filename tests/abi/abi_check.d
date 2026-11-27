// SPDX-License-Identifier: MIT
/++
    Checks the hand-written bindings against the vendored Box3D headers.

    `box3d_c.c` pulls the real headers in through ImportC. At compile time this
    module walks every function, struct and enum the headers declare and checks
    that the D bindings have the same symbol with the same layout: struct size,
    alignment and field offsets, enum member values, and function parameter and
    return types (by size and shape). It also walks every `extern(C)` function the
    bindings declare and takes its address, so the link fails if the library does
    not export it.

    ---
    dub run box3d:abi
    ---
+/
module abi_check;

import std.meta : AliasSeq;
import std.traits;

static import c = box3d_c;
static import d = box3d;
static import box3d.base, box3d.collision, box3d.functions, box3d.id, box3d.math_functions, box3d.types,
    box3d.constants, box3d.snapshot;

/// Names the headers declare that intentionally have no D counterpart.
enum string[] skipped = [
    // Backs the B2_ASSERT macro inside the C sources; not part of the user API.
    "b3InternalAssert",
    // D binds the C union of two bitfield structs as a plain `uint data`
    // (same size and offset); see the comment on the D struct.
    "b3MeshNode",
    // ImportC lays out the anonymous union wrongly: it puts `transform` at 28,
    // where gcc and clang put it at 32 (the union is 8-aligned because of the
    // `hull` pointer). The D struct pads the union to match the real compilers.
    // b3GetCompoundChild returns this struct, so its check trips on the same bug.
    "b3ChildShape", "b3GetCompoundChild",
];

/// True when `name` is a Box3D identifier (as opposed to libc names ImportC
/// pulls in from <math.h>, <stdint.h> and friends).
bool isBox3DName(string name)
{
    import std.algorithm.searching : startsWith;

    return name.startsWith("b3") || name.startsWith("B3_");
}

bool contains(const string[] list, string name)
{
    foreach (s; list)
        if (s == name)
            return true;
    return false;
}

/// Structural comparison of a C type and a D type.
template sameShape(C, D, int depth = 0)
{
    static if (is(C == D))
        enum sameShape = true;
    else static if (C.sizeof != D.sizeof)
        enum sameShape = false;
    else static if (is(C == enum) || is(D == enum))
        enum sameShape = sameShape!(OriginalType!C, OriginalType!D, depth);
    else static if (is(C == const U, U) || is(D == const V, V))
        enum sameShape = sameShape!(Unconst!C, Unconst!D, depth);
    else static if (isFunctionPointer!C && isFunctionPointer!D)
        enum sameShape = sameSignature!(PointerTarget!C, PointerTarget!D, depth + 1);
    else static if (is(C == U*, U) && is(D == V*, V))
    {
        static if (is(Unconst!U == void) || is(Unconst!V == void))
            enum sameShape = is(Unconst!U == void) && is(Unconst!V == void);
        else static if (is(Unconst!U == struct) && is(Unconst!V == struct))
            enum sameShape = __traits(identifier, Unconst!U) == __traits(identifier, Unconst!V);
        else static if (isFunctionPointer!(U*) || isFunctionPointer!(V*))
            enum sameShape = isFunctionPointer!(U*) && isFunctionPointer!(V*) && sameSignature!(U, V, depth + 1);
        else
            enum sameShape = sameShape!(U, V, depth + 1);
    }
    else static if (is(C == struct) && is(D == struct))
        enum sameShape = sameLayout!(C, D, depth);
    else static if (is(C == union) && is(D == union))
        enum sameShape = sameLayout!(C, D, depth);
    else static if (isStaticArray!C && isStaticArray!D)
        enum sameShape = C.length == D.length && sameShape!(typeof(C.init[0]), typeof(D.init[0]), depth);
    else static if (isScalarType!C && isScalarType!D)
        enum sameShape = isFloatingPoint!C == isFloatingPoint!D;
    else
        enum sameShape = false;
}

/// Same size, alignment, and the same named fields at the same offsets.
template sameLayout(C, D, int depth)
{
    static if (C.sizeof != D.sizeof || C.alignof != D.alignof || C.tupleof.length != D.tupleof.length)
        enum sameLayout = false;
    else static if (depth > 4)
        enum sameLayout = true;
    else
        enum sameLayout = () {
            static foreach (i; 0 .. C.tupleof.length)
                {
                if (C.tupleof[i].offsetof != D.tupleof[i].offsetof)
                    return false;
                static if (!sameShape!(typeof(C.tupleof[i]), typeof(D.tupleof[i]), depth + 1))
                    return false;
            }
            return true;
        }();
}

template sameSignature(CF, DF, int depth)
{
    static if (Parameters!CF.length != Parameters!DF.length)
        enum sameSignature = false;
    else
        enum sameSignature = () {
            static if (!sameShape!(ReturnType!CF, ReturnType!DF, depth))
                return false;
            static foreach (i; 0 .. Parameters!CF.length)
                {
                // A C array parameter decays to a pointer; D binds it as `ref T[n]`.
                static if (ParameterStorageClassTuple!DF[i] & ParameterStorageClass.ref_)
                    {
                    static if (!(is(Parameters!CF[i] == P*, P) && isStaticArray!(Parameters!DF[i])
                            && sameShape!(P, typeof(Parameters!DF[i].init[0]), depth)))
                        return false;
                }
                else static if (!sameShape!(Parameters!CF[i], Parameters!DF[i], depth))
                    return false;
            }
            return true;
        }();
}

/// Field-by-field description of a mismatch, for the error message.
string describe(C, D)()
{
    string s = C.stringof ~ ": C size " ~ C.sizeof.stringof ~ " vs D " ~ D.sizeof.stringof;
    static if (is(C == struct) && is(D == struct))
    {
        s ~= "\n    C fields:";
        static foreach (i; 0 .. C.tupleof.length)
            s ~= " " ~ __traits(identifier, C.tupleof[i]) ~ "@" ~ C.tupleof[i].offsetof.stringof;
        s ~= "\n    D fields:";
        static foreach (i; 0 .. D.tupleof.length)
            s ~= " " ~ __traits(identifier, D.tupleof[i]) ~ "@" ~ D.tupleof[i].offsetof.stringof;
    }
    return s;
}

int main()
{
    import std.stdio : writeln;

    int failures;
    int checked;

    // Headers -> bindings.
    static foreach (name; __traits(allMembers, c))
    {
        static if (isBox3DName(name) && !contains(skipped, name) && __traits(compiles, __traits(getMember, c, name)))
        {
            {
                alias CSym = __traits(getMember, c, name);
                static if (is(CSym == struct) || is(CSym == union) || is(CSym == enum) || isFunction!CSym || is(CSym == function))
                {
                    checked++;
                    static if (!__traits(hasMember, d, name))
                    {
                        writeln("missing in D: ", name);
                        failures++;
                    }
                    else
                    {
                        alias DSym = __traits(getMember, d, name);
                        static if (is(CSym == function))
                        {
                            // `typedef R Name(Args)`: D binds it as a function pointer alias.
                            static if (!(isFunctionPointer!DSym && sameSignature!(CSym, PointerTarget!DSym, 0)))
                            {
                                writeln("callback type mismatch: ", name, "\n    C: ", CSym.stringof,
                                        "\n    D: ", DSym.stringof);
                                failures++;
                            }
                        }
                        else static if (isFunction!CSym)
                        {
                            static if (!isFunction!DSym)
                            {
                                writeln("not a function in D: ", name);
                                failures++;
                            }
                            else static if (!sameSignature!(typeof(CSym), typeof(DSym), 0))
                            {
                                writeln("signature mismatch: ", name, "\n    C: ", typeof(CSym).stringof,
                                        "\n    D: ", typeof(DSym).stringof);
                                failures++;
                            }
                        }
                        else static if (is(CSym == enum))
                        {
                            static foreach (m; __traits(allMembers, CSym))
                            {
                                {
                                    static if (!__traits(hasMember, d, m) && !__traits(hasMember, DSym, m))
                                    {
                                        writeln("missing enum member in D: ", name, ".", m);
                                        failures++;
                                    }
                                    else
                                    {
                                        static if (__traits(hasMember, DSym, m))
                                            enum dv = cast(long) __traits(getMember, DSym, m);
                                        else
                                            enum dv = cast(long) __traits(getMember, d, m);
                                        if (cast(long) __traits(getMember, CSym, m) != dv)
                                        {
                                            writeln("enum value mismatch: ", name, ".", m);
                                            failures++;
                                        }
                                    }
                                }
                            }
                        }
                        else static if (__traits(compiles, CSym.sizeof) && __traits(compiles, CSym.tupleof))
                        {
                            static if (!sameShape!(CSym, DSym))
                            {
                                writeln("layout mismatch: ", describe!(CSym, DSym)());
                                failures++;
                            }
                        }
                    }
                }
            }
        }
    }

    // Bindings -> headers, and force every extern(C) declaration to link.
    static foreach (mod; AliasSeq!(box3d.base, box3d.collision, box3d.functions, box3d.id,
            box3d.math_functions, box3d.types, box3d.constants, box3d.snapshot))
    {
        static foreach (name; __traits(allMembers, mod))
        {
            static if (__traits(compiles, __traits(getMember, mod, name)))
            {
                {
                    alias DSym = __traits(getMember, mod, name);
                    static if (isFunction!DSym && functionLinkage!DSym == "C")
                    {
                        static if (!__traits(hasMember, c, name))
                        {
                            writeln("D declares a function the headers do not: ", name);
                            failures++;
                        }
                        else
                        {
                            auto fp = &DSym;
                            if (fp is null)
                                failures++;
                        }
                    }
                }
            }
        }
    }

    writeln(checked, " header declarations checked, ", failures, " problem(s)");
    return failures == 0 ? 0 : 1;
}
