use rustc_middle::{
    mir::{BasicBlockPathResolver, StableBasicBlockDataRef},
    ty::{query::Providers, InstanceBasicBlock, InstanceDef, TyCtxt},
};

pub fn mir_stable_block_path_resolver<'tcx>(
    tcx: TyCtxt<'tcx>,
    key: InstanceDef<'tcx>,
) -> Option<&'tcx BasicBlockPathResolver> {
    let body = tcx.instance_mir(key);
    tcx.arena.alloc(BasicBlockPathResolver::new(body)).as_ref()
}

pub fn mir_stable_block_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    key: InstanceBasicBlock<'tcx>,
) -> Option<StableBasicBlockDataRef<'tcx>> {
    let resolver = tcx.mir_stable_block_path_resolver(key.instance_def)?;
    let basic_block = resolver.block_for_path(key.basic_block_path);
    let body = tcx.instance_mir(key.instance_def);
    let data = &body.basic_blocks()[basic_block];
    Some(StableBasicBlockDataRef::new(data, resolver))
}

pub fn provide(providers: &mut Providers) {
    *providers = Providers { mir_stable_block_path_resolver, mir_stable_block_ref, ..*providers };
}
