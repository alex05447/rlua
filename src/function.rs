use std::os::raw::{c_int, c_void};
use std::ptr;

use crate::error::{Error, Result};
use crate::ffi;
use crate::types::LuaRef;
use crate::util::{
    assert_stack, check_stack, error_traceback, pop_error, protect_lua_closure, StackGuard,
};
use crate::value::{FromLuaMulti, MultiValue, ToLuaMulti};

/// Handle to an internal Lua function.
#[derive(Clone, Debug)]
pub struct Function<'lua>(pub(crate) LuaRef<'lua>);

impl<'lua> Function<'lua> {
    /// Calls the function, passing `args` as function arguments.
    ///
    /// The function's return values are converted to the generic type `R`.
    ///
    /// # Examples
    ///
    /// Call Lua's built-in `tostring` function:
    ///
    /// ```
    /// # use rlua::{Lua, Function, Result};
    /// # fn main() -> Result<()> {
    /// # Lua::new().context(|lua_context| {
    /// let globals = lua_context.globals();
    ///
    /// let tostring: Function = globals.get("tostring")?;
    ///
    /// assert_eq!(tostring.call::<_, String>(123)?, "123");
    ///
    /// # Ok(())
    /// # })
    /// # }
    /// ```
    ///
    /// Call a function with multiple arguments:
    ///
    /// ```
    /// # use rlua::{Lua, Function, Result};
    /// # fn main() -> Result<()> {
    /// # Lua::new().context(|lua_context| {
    /// let sum: Function = lua_context.load(
    ///     r#"
    ///         function(a, b)
    ///             return a + b
    ///         end
    ///     "#).eval()?;
    ///
    /// assert_eq!(sum.call::<_, u32>((3, 4))?, 3 + 4);
    ///
    /// # Ok(())
    /// # })
    /// # }
    /// ```
    pub fn call<A: ToLuaMulti<'lua>, R: FromLuaMulti<'lua>>(&self, args: A) -> Result<R> {
        let lua = self.0.lua;

        let args = args.to_lua_multi(lua)?;
        let nargs = args.len() as c_int;

        let results = unsafe {
            let _sg = StackGuard::new(lua.state);
            check_stack(lua.state, nargs + 3)?;

            ffi::lua_pushcfunction(lua.state, error_traceback);
            let stack_start = ffi::lua_gettop(lua.state);
            lua.push_ref(&self.0);
            for arg in args {
                lua.push_value(arg)?;
            }
            let ret = ffi::lua_pcall(lua.state, nargs, ffi::LUA_MULTRET, stack_start);
            if ret != ffi::LUA_OK {
                return Err(pop_error(lua.state, ret));
            }
            let nresults = ffi::lua_gettop(lua.state) - stack_start;
            let mut results = MultiValue::new();
            assert_stack(lua.state, 2);
            for _ in 0..nresults {
                results.push_front(lua.pop_value());
            }
            ffi::lua_pop(lua.state, 1);
            results
        };
        R::from_lua_multi(results, lua)
    }

    /// Returns a function that, when called, calls `self`, passing `args` as the first set of
    /// arguments.
    ///
    /// If any arguments are passed to the returned function, they will be passed after `args`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rlua::{Lua, Function, Result};
    /// # fn main() -> Result<()> {
    /// # Lua::new().context(|lua_context| {
    /// let sum: Function = lua_context.load(r#"
    ///     function(a, b)
    ///         return a + b
    ///     end
    /// "#).eval()?;
    ///
    /// let bound_a = sum.bind(1)?;
    /// assert_eq!(bound_a.call::<_, u32>(2)?, 1 + 2);
    ///
    /// let bound_a_and_b = sum.bind(13)?.bind(57)?;
    /// assert_eq!(bound_a_and_b.call::<_, u32>(())?, 13 + 57);
    ///
    /// # Ok(())
    /// # })
    /// # }
    /// ```
    pub fn bind<A: ToLuaMulti<'lua>>(&self, args: A) -> Result<Function<'lua>> {
        unsafe extern "C" fn bind_call_impl(state: *mut ffi::lua_State) -> c_int {
            let nargs = ffi::lua_gettop(state);
            let nbinds = ffi::lua_tointeger(state, ffi::lua_upvalueindex(2)) as c_int;
            ffi::luaL_checkstack(state, nbinds + 2, ptr::null());

            ffi::lua_settop(state, nargs + nbinds + 1);
            ffi::lua_rotate(state, -(nargs + nbinds + 1), nbinds + 1);

            ffi::lua_pushvalue(state, ffi::lua_upvalueindex(1));
            ffi::lua_replace(state, 1);

            for i in 0..nbinds {
                ffi::lua_pushvalue(state, ffi::lua_upvalueindex(i + 3));
                ffi::lua_replace(state, i + 2);
            }

            ffi::lua_call(state, nargs + nbinds, ffi::LUA_MULTRET);
            ffi::lua_gettop(state)
        }

        let lua = self.0.lua;

        let args = args.to_lua_multi(lua)?;
        let nargs = args.len() as c_int;

        if nargs + 2 > ffi::LUA_MAX_UPVALUES {
            return Err(Error::BindError);
        }

        unsafe {
            let _sg = StackGuard::new(lua.state);
            check_stack(lua.state, nargs + 5)?;
            lua.push_ref(&self.0);
            ffi::lua_pushinteger(lua.state, nargs as ffi::lua_Integer);
            for arg in args {
                lua.push_value(arg)?;
            }

            protect_lua_closure(lua.state, nargs + 2, 1, |state| {
                ffi::lua_pushcclosure(state, bind_call_impl, nargs + 2);
            })?;

            Ok(Function(lua.pop_ref()))
        }
    }

    /// Dumps the function bytecode using [`lua_dump`](https://www.lua.org/manual/5.3/manual.html#lua_dump).
    pub fn dump(&self) -> Result<Box<[u8]>> {
        let lua = self.0.lua;

        let bytes = unsafe {
            let _sg = StackGuard::new(lua.state);
            check_stack(lua.state, 1)?;

            lua.push_ref(&self.0);

            let mut bytes = Vec::<u8>::new();

            let ud = &mut bytes as *const _ as *mut c_void;

            let ret = ffi::lua_dump(lua.state, lua_Writer_impl, ud, 1);

            if ret != ffi::LUA_OK {
                return Err(Error::MemoryError(
                    "Failed to write the function bytecode - out of memory?".to_owned(),
                ));
            }

            bytes.into_boxed_slice()
        };

        Ok(bytes)
    }
}

#[allow(non_snake_case)]
unsafe extern "C" fn lua_Writer_impl(
    _state: *mut ffi::lua_State,
    p: *const c_void,
    sz: usize,
    ud: *mut c_void,
) -> c_int {
    use std::io::Write;

    let bytes: &mut Vec<u8> = &mut *(ud as *mut _);

    let src: &[u8] = std::slice::from_raw_parts(p as *const _, sz);

    match bytes.write(src) {
        Ok(written) => {
            if written == sz {
                0
            } else {
                1
            }
        }
        Err(_) => 1,
    }
}
