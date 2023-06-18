#[cfg(test)]
mod tests {
    use inkwell::context::Context;

    use crate::{parser, check, compile};

    #[test]
    fn it_works() -> Result<(), ()> {
        let fp = parser::FileParser::new("./benchmark/hash.mpl").map_err(|_|())?;
        let mut ast = fp.parse().map_err(|_|())?;
        check(&mut ast);
        let context = Context::create();
        let builder = &context.create_builder();
        let module = &context.create_module("module");
        let compiler = compile::compile(&context, builder, module, ast);
		unsafe { compiler.get_function::<unsafe extern "C" fn(i64) -> i64>("fillAndLoop").call(100)};
        Ok(())
    }
}
