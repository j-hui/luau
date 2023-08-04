// This file is part of the Luau programming language and is licensed under MIT License; see LICENSE.txt for details
// This code is based on Lua 5.x implementation licensed under MIT License; see lua_LICENSE.txt for details
#include "ldo.h"
#include "lobject.h"
#include "lua.h"
#include "lualib.h"
#include "lvm.h"

#include "lstate.h"
#include "ltable.h"
#include "lfunc.h"
#include "lstring.h"
#include "lgc.h"
#include "lmem.h"
#include "lbytecode.h"
#include "lapi.h"

#include <string.h>

LUAU_FASTFLAGVARIABLE(LuauLoadCheckGC, false)

// TODO: RAII deallocation doesn't work for longjmp builds if a memory error happens
template<typename T>
struct TempBuffer
{
    lua_State* L;
    T* data;
    size_t count;

    TempBuffer(lua_State* L, size_t count)
        : L(L)
        , data(luaM_newarray(L, count, T, 0))
        , count(count)
    {
    }

    ~TempBuffer()
    {
        luaM_freearray(L, data, count, T, 0);
    }

    T& operator[](size_t index)
    {
        LUAU_ASSERT(index < count);
        return data[index];
    }
};

void luaV_getimport(lua_State* L, Table* env, TValue* k, StkId res, uint32_t id, bool propagatenil)
{
    int count = id >> 30;
    LUAU_ASSERT(count > 0);

    int id0 = int(id >> 20) & 1023;
    int id1 = int(id >> 10) & 1023;
    int id2 = int(id) & 1023;

    // after the first call to luaV_gettable, res may be invalid, and env may (sometimes) be garbage collected
    // we take care to not use env again and to restore res before every consecutive use
    ptrdiff_t resp = savestack(L, res);

    // global lookup for id0
    TValue g;
    sethvalue(L, &g, env);
    luaV_gettable(L, &g, &k[id0], res);

    // table lookup for id1
    if (count < 2)
        return;

    res = restorestack(L, resp);
    if (!propagatenil || !ttisnil(res))
        luaV_gettable(L, res, &k[id1], res);

    // table lookup for id2
    if (count < 3)
        return;

    res = restorestack(L, resp);
    if (!propagatenil || !ttisnil(res))
        luaV_gettable(L, res, &k[id2], res);
}

template<typename T>
static T read(const char* data, size_t size, size_t& offset)
{
    T result;
    memcpy(&result, data + offset, sizeof(T));
    offset += sizeof(T);

    return result;
}

static unsigned int readVarInt(const char* data, size_t size, size_t& offset)
{
    unsigned int result = 0;
    unsigned int shift = 0;

    uint8_t byte;

    do
    {
        byte = read<uint8_t>(data, size, offset);
        result |= (byte & 127) << shift;
        shift += 7;
    } while (byte & 128);

    return result;
}

static TString* readString(TempBuffer<TString*>& strings, const char* data, size_t size, size_t& offset)
{
    unsigned int id = readVarInt(data, size, offset);

    return id == 0 ? NULL : strings[id - 1];
}

static void resolveImportSafe(lua_State* L, Table* env, TValue* k, uint32_t id)
{
    struct ResolveImport
    {
        TValue* k;
        uint32_t id;

        static void run(lua_State* L, void* ud)
        {
            ResolveImport* self = static_cast<ResolveImport*>(ud);

            // note: we call getimport with nil propagation which means that accesses to table chains like A.B.C will resolve in nil
            // this is technically not necessary but it reduces the number of exceptions when loading scripts that rely on getfenv/setfenv for global
            // injection
            // allocate a stack slot so that we can do table lookups
            luaD_checkstack(L, 1);
            setnilvalue(L->top);
            L->top++;

            luaV_getimport(L, L->gt, self->k, L->top - 1, self->id, /* propagatenil= */ true);
        }
    };

    ResolveImport ri = {k, id};
    if (L->gt->safeenv)
    {
        // luaD_pcall will make sure that if any C/Lua calls during import resolution fail, the thread state is restored back
        int oldTop = lua_gettop(L);
        int status = luaD_pcall(L, &ResolveImport::run, &ri, savestack(L, L->top), 0);
        LUAU_ASSERT(oldTop + 1 == lua_gettop(L)); // if an error occurred, luaD_pcall saves it on stack

        if (status != 0)
        {
            // replace error object with nil
            setnilvalue(L->top - 1);
        }
    }
    else
    {
        setnilvalue(L->top);
        L->top++;
    }
}

int luau_load(lua_State* L, const char* chunkname, const char* data, size_t size, int env)
{
    size_t offset = 0;

    uint8_t version = read<uint8_t>(data, size, offset);



    // 0 means the rest of the bytecode is the error message
    if (version == 0)
    {
        char chunkbuf[LUA_IDSIZE];
        const char* chunkid = luaO_chunkid(chunkbuf, sizeof(chunkbuf), chunkname, strlen(chunkname));
        lua_pushfstring(L, "%s%.*s", chunkid, int(size - offset), data + offset);
        return 1;
    }

    if (version < LBC_VERSION_MIN || version > LBC_VERSION_MAX)
    {
        char chunkbuf[LUA_IDSIZE];
        const char* chunkid = luaO_chunkid(chunkbuf, sizeof(chunkbuf), chunkname, strlen(chunkname));
        lua_pushfstring(L, "%s: bytecode version mismatch (expected [%d..%d], got %d)", chunkid, LBC_VERSION_MIN, LBC_VERSION_MAX, version);
        return 1;
    }

    // we will allocate a fair amount of memory so check GC before we do
    if (FFlag::LuauLoadCheckGC)
        luaC_checkGC(L);

    // pause GC for the duration of deserialization - some objects we're creating aren't rooted
    // TODO: if an allocation error happens mid-load, we do not unpause GC!
    size_t GCthreshold = L->global->GCthreshold;
    L->global->GCthreshold = SIZE_MAX;

    // env is 0 for current environment and a stack index otherwise
    Table* envt = (env == 0) ? L->gt : hvalue(luaA_toobject(L, env));

    TString* source = luaS_new(L, chunkname);

    uint8_t typesversion = 0;

    if (version >= 4)
    {
        typesversion = read<uint8_t>(data, size, offset);
    }

    // string table
    unsigned int stringCount = readVarInt(data, size, offset);
    TempBuffer<TString*> strings(L, stringCount);

    for (unsigned int i = 0; i < stringCount; ++i)
    {
        unsigned int length = readVarInt(data, size, offset);

        strings[i] = luaS_newlstr(L, data + offset, length);
        offset += length;
    }

    // proto table
    unsigned int protoCount = readVarInt(data, size, offset);
    TempBuffer<Proto*> protos(L, protoCount);

    for (unsigned int i = 0; i < protoCount; ++i)
    {
        Proto* p = luaF_newproto(L);
        p->source = source;
        p->bytecodeid = int(i);

        p->maxstacksize = read<uint8_t>(data, size, offset);
        p->numparams = read<uint8_t>(data, size, offset);
        p->nups = read<uint8_t>(data, size, offset);
        p->is_vararg = read<uint8_t>(data, size, offset);

        if (version >= 4)
        {
            p->flags = read<uint8_t>(data, size, offset);

            uint32_t typesize = readVarInt(data, size, offset);

            if (typesize && typesversion == LBC_TYPE_VERSION)
            {
                uint8_t* types = (uint8_t*)data + offset;

                LUAU_ASSERT(typesize == unsigned(2 + p->numparams));
                LUAU_ASSERT(types[0] == LBC_TYPE_FUNCTION);
                LUAU_ASSERT(types[1] == p->numparams);

                p->typeinfo = luaM_newarray(L, typesize, uint8_t, p->memcat);
                memcpy(p->typeinfo, types, typesize);
            }

            offset += typesize;
        }

        p->sizecode = readVarInt(data, size, offset);
        p->code = luaM_newarray(L, p->sizecode, Instruction, p->memcat);
        for (int j = 0; j < p->sizecode; ++j)
            p->code[j] = read<uint32_t>(data, size, offset);

        p->codeentry = p->code;

        p->sizek = readVarInt(data, size, offset);
        p->k = luaM_newarray(L, p->sizek, TValue, p->memcat);

#ifdef HARDMEMTESTS
        // this is redundant during normal runs, but resolveImportSafe can trigger GC checks under HARDMEMTESTS
        // because p->k isn't fully formed at this point, we pre-fill it with nil to make subsequent setup safe
        for (int j = 0; j < p->sizek; ++j)
        {
            setnilvalue(&p->k[j]);
        }
#endif

        for (int j = 0; j < p->sizek; ++j)
        {
            switch (read<uint8_t>(data, size, offset))
            {
            case LBC_CONSTANT_NIL:
                setnilvalue(&p->k[j]);
                break;

            case LBC_CONSTANT_BOOLEAN:
            {
                uint8_t v = read<uint8_t>(data, size, offset);
                setbvalue(&p->k[j], v);
                break;
            }

            case LBC_CONSTANT_NUMBER:
            {
                double v = read<double>(data, size, offset);
                setnvalue(&p->k[j], v);
                break;
            }

            case LBC_CONSTANT_STRING:
            {
                TString* v = readString(strings, data, size, offset);
                setsvalue(L, &p->k[j], v);
                break;
            }

            case LBC_CONSTANT_IMPORT:
            {
                uint32_t iid = read<uint32_t>(data, size, offset);
                resolveImportSafe(L, envt, p->k, iid);
                setobj(L, &p->k[j], L->top - 1);
                L->top--;
                break;
            }

            case LBC_CONSTANT_TABLE:
            {
                int keys = readVarInt(data, size, offset);
                Table* h = luaH_new(L, 0, keys);
                for (int i = 0; i < keys; ++i)
                {
                    int key = readVarInt(data, size, offset);
                    TValue* val = luaH_set(L, h, &p->k[key]);
                    setnvalue(val, 0.0);
                }
                sethvalue(L, &p->k[j], h);
                break;
            }

            case LBC_CONSTANT_CLOSURE:
            {
                uint32_t fid = readVarInt(data, size, offset);
                Closure* cl = luaF_newLclosure(L, protos[fid]->nups, envt, protos[fid]);
                cl->preload = (cl->nupvalues > 0);
                setclvalue(L, &p->k[j], cl);
                break;
            }

            default:
                LUAU_ASSERT(!"Unexpected constant kind");
            }
        }

        p->sizep = readVarInt(data, size, offset);
        p->p = luaM_newarray(L, p->sizep, Proto*, p->memcat);
        for (int j = 0; j < p->sizep; ++j)
        {
            uint32_t fid = readVarInt(data, size, offset);
            p->p[j] = protos[fid];
        }

        p->linedefined = readVarInt(data, size, offset);
        p->debugname = readString(strings, data, size, offset);

        uint8_t lineinfo = read<uint8_t>(data, size, offset);

        if (lineinfo)
        {
            p->linegaplog2 = read<uint8_t>(data, size, offset);

            int intervals = ((p->sizecode - 1) >> p->linegaplog2) + 1;
            int absoffset = (p->sizecode + 3) & ~3;

            p->sizelineinfo = absoffset + intervals * sizeof(int);
            p->lineinfo = luaM_newarray(L, p->sizelineinfo, uint8_t, p->memcat);
            p->abslineinfo = (int*)(p->lineinfo + absoffset);

            uint8_t lastoffset = 0;
            for (int j = 0; j < p->sizecode; ++j)
            {
                lastoffset += read<uint8_t>(data, size, offset);
                p->lineinfo[j] = lastoffset;
            }

            int lastline = 0;
            for (int j = 0; j < intervals; ++j)
            {
                lastline += read<int32_t>(data, size, offset);
                p->abslineinfo[j] = lastline;
            }
        }

        uint8_t debuginfo = read<uint8_t>(data, size, offset);

        if (debuginfo)
        {
            p->sizelocvars = readVarInt(data, size, offset);
            p->locvars = luaM_newarray(L, p->sizelocvars, LocVar, p->memcat);

            for (int j = 0; j < p->sizelocvars; ++j)
            {
                p->locvars[j].varname = readString(strings, data, size, offset);
                p->locvars[j].startpc = readVarInt(data, size, offset);
                p->locvars[j].endpc = readVarInt(data, size, offset);
                p->locvars[j].reg = read<uint8_t>(data, size, offset);
            }

            p->sizeupvalues = readVarInt(data, size, offset);
            p->upvalues = luaM_newarray(L, p->sizeupvalues, TString*, p->memcat);

            for (int j = 0; j < p->sizeupvalues; ++j)
            {
                p->upvalues[j] = readString(strings, data, size, offset);
            }
        }

        protos[i] = p;
    }

    // "main" proto is pushed to Lua stack
    uint32_t mainid = readVarInt(data, size, offset);
    Proto* main = protos[mainid];

    luaC_threadbarrier(L);

    Closure* cl = luaF_newLclosure(L, 0, envt, main);
    setclvalue(L, L->top, cl);
    incr_top(L);

    L->global->GCthreshold = GCthreshold;

    return 0;
}

static void pinproto(lua_State* L, TString* k, Table* t, struct Proto* p)
{
    // Tell proto what its key is
    p->pinkey = k;

    // Add proto pointer to lookup table; it's ok if the entry is already there,
    // it will just be overwritten by the same pointer.
    setptvalue(L, luaH_setnum(L, t, p->bytecodeid), p);

    // NOTE: Yes, we're using recursion for DFS but I do not know what is the
    // data structure du jour that I should use for vector.
    for (int i = 0; i < p->sizep; ++i)
        pinproto(L, k, t, p->p[i]);
}

void lua_registerfkey(lua_State* L, const char* key, size_t keylen)
{
    // TODO: thread barriers?
    int t = lua_type(L, 1);
    luaL_argexpected(L, t != LUA_TFUNCTION, 1, "function");

    struct Closure* c = clvalue(L->top - 1);
    luaL_argexpected(L, c->isC, 1, "Luau function");

    struct Proto* p = c->l.p;
    L->top--;

    TString* k = luaS_newlstr(L, key, keylen);
    // NOTE: it would be really nice to know how many protos we have...
    Table* lookup_tbl = luaH_new(L, 1, 0);

    // Get global _PROTOS table (or create it if it doesn't exist)
    lua_getfield(L, LUA_REGISTRYINDEX, "_PROTOS");
    // Stack: _PROTOS|nil
    if (lua_isnil(L, -1))
    {
        // Doesn't exist; create _PROTOS table
        // Stack: nil
        lua_pop(L, 1);
        // Stack:
        lua_createtable(L, 0, 1);
        // Stack: _PROTOS
        lua_pushvalue(L, -1);
        // Stack: _PROTOS, _PROTOS
        lua_setfield(L, LUA_REGISTRYINDEX, "_PROTOS");
    }

    // Check if _PROTOS[k] already exists
    // Stack: _PROTOS
    setsvalue(L, L->top, k);
    incr_top(L);
    // Stack: _PROTOS, k
    lua_rawget(L, -2);
    // Stack: _PROTOS, _PROTOS[k]|nil
    if (!lua_isnil(L, -1))
    {
        // _PROTOS[k] already exists
        // TODO: throw an error
    }

    // Stack: _PROTOS, nil
    lua_pop(L, 1);

    // Set _PROTOS[k] to lookup_tbl
    // Stack: _PROTOS
    setsvalue(L, L->top, k);
    incr_top(L);
    // Stack: _PROTOS, k
    sethvalue(L, L->top, lookup_tbl);
    incr_top(L);
    // Stack: _PROTOS, k, lookup_tbl
    lua_rawset(L, 1);
    // Stack: _PROTOS
    lua_pop(L, 1);
    // Stack:

    // Populate lookup_tbl + install key in protos
    pinproto(L, k, lookup_tbl, p);
}

void lua_unregisterfkey(lua_State* L, const char* key, size_t keylen)
{
    // TODO: this
}

void lua_getfkey(lua_State* L)
{
    StkId arg = L->top - 1;
    // TODO: thread barriers?
    if (!ttisfunction(arg) || clvalue(arg)->isC)
    {
        setnilvalue(L->top - 1);
        lua_pushstring(L, "expected Luau function");
        return;
    }

    struct Proto* p = clvalue(arg)->l.p;

    if (p->pinkey == NULL)
    {
        setnilvalue(L->top - 1);
        lua_pushstring(L, "function is not pinned");
        return;
    }

    setsvalue(L, L->top - 1, p->pinkey);
    lua_pushinteger(L, p->bytecodeid);
}

void lua_lookupfkey(lua_State* L)
{
    api_check(L, 2 <= (L->top - L->base));
    if (!ttisstring(L->top - 1) || !ttisnumber(L->top - 2))
    {
        // Key has to be a string
        setnilvalue(L->top - 1);
        return;
    }

    TString* k = tsvalue(L->top - 1);
    int i = int(nvalue(L->top - 2));

    L->top -= 2;

    // Get global _PROTOS table (or create it if it doesn't exist)
    lua_getfield(L, LUA_REGISTRYINDEX, "_PROTOS");
    // Stack: _PROTOS|nil
    if (lua_isnil(L, -1))
    {
        // Doesn't exist; TODO: throw error
    }

    // Stack: _PROTOS
    lua_rawgetfield(L, -1, getstr(k));
    // Stack: _PROTOS, _PROTOS[k]|nil
    setobj2s(L, L->top - 2, L->top - 1);
    L->top--;
    // Stack: _PROTOS[k]|nil
    if (lua_isnil(L, -1))
    {
        // Stack: nil
        return;
    }
    // Stack: _PROTOS[k]
    Table* t = hvalue(L->top - 1);
    L->top--;
    // Stack:
    const TValue* v = luaH_getnum(t, i);
    if (ttype(v) != LUA_TPROTO)
    {
        lua_pushnil(L);
        // Stack: nil
        return;
    }
    Proto* p = &v->value.gc->p;
    Closure* c = luaF_newLclosure(L, p->nups, L->gt, p);
    setclvalue(L, L->top, c);
    incr_top(L);
    // Stack: closure
}
