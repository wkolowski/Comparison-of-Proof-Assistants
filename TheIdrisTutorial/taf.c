#include "math.h"
#include "idris_rts.h"
#include "idris_bitstring.h"
#include "idris_stdfgn.h"
void* _idris_assert_95_unreachable(VM*, VAL*);
void* _idris_call_95__95_IO(VM*, VAL*);
void* _idris_Prelude_46_Interactive_46_getLine_39_(VM*, VAL*);
void* _idris_Main_46_greet(VM*, VAL*);
void* _idris_idris_95_crash(VM*, VAL*);
void* _idris_Prelude_46_Interfaces_46_intToBool(VM*, VAL*);
void* _idris_io_95_bind(VM*, VAL*);
void* _idris_io_95_pure(VM*, VAL*);
void* _idris_Main_46_main(VM*, VAL*);
void* _idris_mkForeignPrim(VM*, VAL*);
void* _idris_Prelude_46_Bool_46_not(VM*, VAL*);
void* _idris_prim_95__95_asPtr(VM*, VAL*);
void* _idris_prim_95__95_concat(VM*, VAL*);
void* _idris_prim_95__95_eqManagedPtr(VM*, VAL*);
void* _idris_prim_95__95_eqPtr(VM*, VAL*);
void* _idris_prim_95__95_eqString(VM*, VAL*);
void* _idris_prim_95__95_managedNull(VM*, VAL*);
void* _idris_prim_95__95_null(VM*, VAL*);
void* _idris_prim_95__95_peek16(VM*, VAL*);
void* _idris_prim_95__95_peek32(VM*, VAL*);
void* _idris_prim_95__95_peek64(VM*, VAL*);
void* _idris_prim_95__95_peek8(VM*, VAL*);
void* _idris_prim_95__95_peekDouble(VM*, VAL*);
void* _idris_prim_95__95_peekPtr(VM*, VAL*);
void* _idris_prim_95__95_peekSingle(VM*, VAL*);
void* _idris_prim_95__95_poke16(VM*, VAL*);
void* _idris_prim_95__95_poke32(VM*, VAL*);
void* _idris_prim_95__95_poke64(VM*, VAL*);
void* _idris_prim_95__95_poke8(VM*, VAL*);
void* _idris_prim_95__95_pokeDouble(VM*, VAL*);
void* _idris_prim_95__95_pokePtr(VM*, VAL*);
void* _idris_prim_95__95_pokeSingle(VM*, VAL*);
void* _idris_prim_95__95_ptrOffset(VM*, VAL*);
void* _idris_prim_95__95_readChars(VM*, VAL*);
void* _idris_prim_95__95_readFile(VM*, VAL*);
void* _idris_prim_95__95_readString(VM*, VAL*);
void* _idris_prim_95__95_registerPtr(VM*, VAL*);
void* _idris_prim_95__95_sizeofPtr(VM*, VAL*);
void* _idris_prim_95__95_stderr(VM*, VAL*);
void* _idris_prim_95__95_stdin(VM*, VAL*);
void* _idris_prim_95__95_stdout(VM*, VAL*);
void* _idris_prim_95__95_strCons(VM*, VAL*);
void* _idris_prim_95__95_strHead(VM*, VAL*);
void* _idris_prim_95__95_strRev(VM*, VAL*);
void* _idris_prim_95__95_strTail(VM*, VAL*);
void* _idris_prim_95__95_vm(VM*, VAL*);
void* _idris_prim_95__95_writeFile(VM*, VAL*);
void* _idris_prim_95__95_writeString(VM*, VAL*);
void* _idris_prim_95_io_95_bind(VM*, VAL*);
void* _idris_run_95__95_IO(VM*, VAL*);
void* _idris_unsafePerformPrimIO(VM*, VAL*);
void* _idris_world(VM*, VAL*);
void* _idris__123_APPLY_95_0_125_(VM*, VAL*);
void* _idris__123_APPLY2_95_0_125_(VM*, VAL*);
void* _idris__123_EVAL_95_0_125_(VM*, VAL*);
void* _idris__123_runMain_95_0_125_(VM*, VAL*);
void* _idris_Decidable_46_Equality_46_Decidable_46_Equality_46__64_Decidable_46_Equality_46_DecEq_36_Bool_58__33_decEq_58_0(VM*, VAL*);
void* _idris__95_Prelude_46_Interactive_46_getLine_39__58_trimNL_58_0_95_with_95_18(VM*, VAL*);
void* _idris__95_Prelude_46_Strings_46_strM_95_with_95_33(VM*, VAL*);
void* _idris_io_95_bind_95_IO_95__95_idr_95_108_95_34_95_108_95_36_95_case(VM*, VAL*);
void* _idris_assert_95_unreachable(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = NULL;
    TOPBASE(0);
    REBASE;
}

void* _idris_call_95__95_IO(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    LOC(3) = NULL;
    RESERVE(2);
    TOP(0) = LOC(2);
    TOP(1) = LOC(3);
    SLIDE(vm, 2);
    TOPBASE(2);
    TAILCALL(_idris__123_APPLY_95_0_125_);
}

void* _idris_Prelude_46_Interactive_46_getLine_39_(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(5);
    ADDTOP(5);
    LOC(2) = idris_readStr(vm, stdin);
    LOC(3) = idris_strRev(vm, LOC(2));
    LOC(4) = MKSTR(vm, "");
    LOC(3) = idris_streq(vm, LOC(3), LOC(4));
    if (GETINT(LOC(3)) == 0) {
        LOC(3) = NULL_CON(1);
    } else
    {
        LOC(3) = NULL_CON(0);
    }
    LOC(4) = NULL_CON(1);
    RESERVE(2);
    TOP(0) = LOC(3);
    TOP(1) = LOC(4);
    STOREOLD;
    BASETOP(0);
    ADDTOP(2);
    CALL(_idris_Decidable_46_Equality_46_Decidable_46_Equality_46__64_Decidable_46_Equality_46_DecEq_36_Bool_58__33_decEq_58_0);
    LOC(3) = RVAL;
    if (CTAG(LOC(3)) == 1) {
        PROJECT(vm, LOC(3), 4, 0);
        LOC(3) = MKSTR(vm, "");
    }
    else
    {
        PROJECT(vm, LOC(3), 4, 0);
        LOC(4) = idris_strRev(vm, LOC(2));
        LOC(4) = idris_strHead(vm, LOC(4));
        if (GETINT(LOC(4)) == 10) {
            LOC(5) = idris_strRev(vm, LOC(2));
            LOC(3) = idris_strTail(vm, LOC(5));
        } else
        {
            LOC(5) = idris_strRev(vm, LOC(2));
            LOC(5) = idris_strHead(vm, LOC(5));
            LOC(6) = idris_strRev(vm, LOC(2));
            LOC(6) = idris_strTail(vm, LOC(6));
            LOC(3) = idris_strCons(vm, LOC(5),LOC(6));
        }
    }
    RVAL = idris_strRev(vm, LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_Main_46_greet(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(4);
    ADDTOP(4);
    LOC(1) = MKSTR(vm, "Kio estas via nomo?""\x0a""");
    LOC(1) = MKINT((i_int)(idris_writeStr(stdout,GETSTR(LOC(1)))));
    LOC(1) = NULL_CON(0);
    LOC(2) = NULL;
    RESERVE(2);
    TOP(0) = LOC(2);
    TOP(1) = LOC(0);
    STOREOLD;
    BASETOP(0);
    ADDTOP(2);
    CALL(_idris_Prelude_46_Interactive_46_getLine_39_);
    LOC(2) = RVAL;
    LOC(3) = MKSTR(vm, "Saluton, ");
    LOC(4) = MKSTR(vm, "!");
    LOC(4) = idris_concat(vm, LOC(2), LOC(4));
    LOC(3) = idris_concat(vm, LOC(3), LOC(4));
    LOC(4) = MKSTR(vm, """\x0a""");
    LOC(3) = idris_concat(vm, LOC(3), LOC(4));
    LOC(3) = MKINT((i_int)(idris_writeStr(stdout,GETSTR(LOC(3)))));
    RVAL = NULL_CON(0);
    TOPBASE(0);
    REBASE;
}

void* _idris_idris_95_crash(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = NULL;
    TOPBASE(0);
    REBASE;
}

void* _idris_Prelude_46_Interfaces_46_intToBool(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    if (GETINT(LOC(0)) == 0) {
        RVAL = NULL_CON(0);
        TOPBASE(0);
        REBASE;
    } else
    {
        RVAL = NULL_CON(1);
        TOPBASE(0);
        REBASE;
    }
}

void* _idris_io_95_bind(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RESERVE(2);
    TOP(0) = LOC(3);
    TOP(1) = LOC(5);
    STOREOLD;
    BASETOP(0);
    ADDTOP(2);
    CALL(_idris__123_APPLY_95_0_125_);
    LOC(6) = RVAL;
    RESERVE(2);
    TOP(0) = LOC(4);
    TOP(1) = LOC(6);
    STOREOLD;
    BASETOP(0);
    ADDTOP(2);
    CALL(_idris__123_APPLY_95_0_125_);
    LOC(6) = RVAL;
    RESERVE(2);
    TOP(0) = LOC(6);
    TOP(1) = LOC(5);
    SLIDE(vm, 2);
    TOPBASE(2);
    TAILCALL(_idris__123_APPLY_95_0_125_);
}

void* _idris_io_95_pure(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = LOC(2);
    TOPBASE(0);
    REBASE;
}

void* _idris_Main_46_main(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    LOC(1) = MKSTR(vm, "Hello, wurst!""\x0a""");
    LOC(1) = MKINT((i_int)(idris_writeStr(stdout,GETSTR(LOC(1)))));
    LOC(1) = NULL_CON(0);
    RESERVE(1);
    TOP(0) = LOC(0);
    SLIDE(vm, 1);
    TOPBASE(1);
    TAILCALL(_idris_Main_46_greet);
}

void* _idris_mkForeignPrim(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = NULL;
    TOPBASE(0);
    REBASE;
}

void* _idris_Prelude_46_Bool_46_not(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    if (CTAG(LOC(0)) == 0) {
        PROJECT(vm, LOC(0), 1, 0);
        RVAL = NULL_CON(1);
        TOPBASE(0);
        REBASE;
    }
    else
    {
        PROJECT(vm, LOC(0), 1, 0);
        RVAL = NULL_CON(0);
        TOPBASE(0);
        REBASE;
    }
}

void* _idris_prim_95__95_asPtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, GETMPTR(LOC(0)));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_concat(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_concat(vm, LOC(0), LOC(1));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_eqManagedPtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKINT((i_int)(GETMPTR(LOC(0)) == GETMPTR(LOC(1))));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_eqPtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKINT((i_int)(GETPTR(LOC(0)) == GETPTR(LOC(1))));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_eqString(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_streq(vm, LOC(0), LOC(1));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_managedNull(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, NULL);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_null(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, NULL);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peek16(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekB16(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peek32(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekB32(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peek64(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekB64(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peek8(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekB8(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peekDouble(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekDouble(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peekPtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekPtr(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_peekSingle(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_peekSingle(vm,LOC(1),LOC(2));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_poke16(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokeB16(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_poke32(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokeB32(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_poke64(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokeB64(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_poke8(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokeB8(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_pokeDouble(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokeDouble(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_pokePtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokePtr(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_pokeSingle(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_pokeSingle(LOC(1),LOC(2),LOC(3));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_ptrOffset(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, (void *)((char *)GETPTR(LOC(0)) + GETINT(LOC(1))));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_readChars(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_readChars(vm, GETINT(LOC(1)), GETPTR(LOC(2)));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_readFile(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_readStr(vm, GETPTR(LOC(1)));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_readString(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_readStr(vm, stdin);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_registerPtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKMPTR(vm, GETPTR(LOC(0)), GETINT(LOC(1)));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_sizeofPtr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKINT(sizeof(void*));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_stderr(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, stderr);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_stdin(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, stdin);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_stdout(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, stdout);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_strCons(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_strCons(vm, LOC(0),LOC(1));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_strHead(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_strHead(vm, LOC(0));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_strRev(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_strRev(vm, LOC(0));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_strTail(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = idris_strTail(vm, LOC(0));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_vm(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKPTR(vm, vm);
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_writeFile(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKINT((i_int)(idris_writeStr(GETPTR(LOC(1)),GETSTR(LOC(2)))));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95__95_writeString(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = MKINT((i_int)(idris_writeStr(stdout,GETSTR(LOC(1)))));
    TOPBASE(0);
    REBASE;
}

void* _idris_prim_95_io_95_bind(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RESERVE(2);
    TOP(0) = LOC(3);
    TOP(1) = LOC(2);
    SLIDE(vm, 2);
    TOPBASE(2);
    TAILCALL(_idris__123_APPLY_95_0_125_);
}

void* _idris_run_95__95_IO(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    LOC(2) = NULL;
    RESERVE(2);
    TOP(0) = LOC(1);
    TOP(1) = LOC(2);
    SLIDE(vm, 2);
    TOPBASE(2);
    TAILCALL(_idris__123_APPLY_95_0_125_);
}

void* _idris_unsafePerformPrimIO(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = NULL;
    TOPBASE(0);
    REBASE;
}

void* _idris_world(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = LOC(0);
    TOPBASE(0);
    REBASE;
}

void* _idris__123_APPLY_95_0_125_(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = NULL;
    TOPBASE(0);
    REBASE;
}

void* _idris__123_APPLY2_95_0_125_(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RVAL = NULL;
    TOPBASE(0);
    REBASE;
}

void* _idris__123_EVAL_95_0_125_(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    switch(TAG(LOC(0))) {
    default:
        RVAL = LOC(0);
        TOPBASE(0);
        REBASE;
        break;
    }
}

void* _idris__123_runMain_95_0_125_(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    LOC(0) = NULL;
    RESERVE(1);
    TOP(0) = LOC(0);
    STOREOLD;
    BASETOP(0);
    ADDTOP(1);
    CALL(_idris_Main_46_main);
    LOC(0) = RVAL;
    RESERVE(1);
    TOP(0) = LOC(0);
    SLIDE(vm, 1);
    TOPBASE(1);
    TAILCALL(_idris__123_EVAL_95_0_125_);
}

void* _idris_Decidable_46_Equality_46_Decidable_46_Equality_46__64_Decidable_46_Equality_46_DecEq_36_Bool_58__33_decEq_58_0(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    if (CTAG(LOC(1)) == 0) {
        PROJECT(vm, LOC(1), 2, 0);
        if (CTAG(LOC(0)) == 0) {
            PROJECT(vm, LOC(0), 2, 0);
            RVAL = NULL_CON(0);
            TOPBASE(0);
            REBASE;
        }
        else
        {
            PROJECT(vm, LOC(0), 2, 0);
            RVAL = NULL_CON(1);
            TOPBASE(0);
            REBASE;
        }
    }
    else
    {
        PROJECT(vm, LOC(1), 2, 0);
        if (CTAG(LOC(0)) == 0) {
            PROJECT(vm, LOC(0), 2, 0);
            RVAL = NULL_CON(1);
            TOPBASE(0);
            REBASE;
        }
        else
        {
            PROJECT(vm, LOC(0), 2, 0);
            RVAL = NULL_CON(0);
            TOPBASE(0);
            REBASE;
        }
    }
}

void* _idris__95_Prelude_46_Interactive_46_getLine_39__58_trimNL_58_0_95_with_95_18(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(2);
    ADDTOP(2);
    if (CTAG(LOC(2)) == 1) {
        PROJECT(vm, LOC(2), 3, 2);
        if (GETINT(LOC(3)) == 10) {
            RVAL = LOC(4);
            TOPBASE(0);
            REBASE;
        } else
        {
            RVAL = idris_strCons(vm, LOC(3),LOC(4));
            TOPBASE(0);
            REBASE;
        }
    }
    else
    {
        PROJECT(vm, LOC(2), 3, 0);
        RVAL = MKSTR(vm, "");
        TOPBASE(0);
        REBASE;
    }
}

void* _idris__95_Prelude_46_Strings_46_strM_95_with_95_33(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(2);
    ADDTOP(2);
    if (CTAG(LOC(1)) == 1) {
        PROJECT(vm, LOC(1), 2, 0);
        RVAL = NULL_CON(0);
        TOPBASE(0);
        REBASE;
    }
    else
    {
        PROJECT(vm, LOC(1), 2, 0);
        LOC(2) = idris_strHead(vm, LOC(0));
        LOC(3) = idris_strTail(vm, LOC(0));
        allocCon(REG1, vm, 1, 2, 0);
        SETARG(REG1, 0, LOC(2)); SETARG(REG1, 1, LOC(3)); 
        RVAL = REG1;
        TOPBASE(0);
        REBASE;
    }
}

void* _idris_io_95_bind_95_IO_95__95_idr_95_108_95_34_95_108_95_36_95_case(VM* vm, VAL* oldbase) {
    INITFRAME;
loop:
    RESERVE(1);
    ADDTOP(1);
    RESERVE(2);
    TOP(0) = LOC(7);
    TOP(1) = LOC(5);
    SLIDE(vm, 2);
    TOPBASE(2);
    TAILCALL(_idris__123_APPLY_95_0_125_);
}

