// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

use crate::{BfTree, Config, LeafInsertResult};

#[test]
fn drop_does_not_read_base_pages_from_disk() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("tree");
    let mut config = Config::new(&path, 1024 * 1024);
    config
        .leaf_page_size(4096)
        .cb_max_key_len(8)
        .cb_max_record_size(1024)
        .read_promotion_rate(0)
        .scan_promotion_rate(0);
    let tree = BfTree::with_config(config, None).unwrap();
    for id in 0u64..20_000 {
        let key = id.to_be_bytes();
        assert_eq!(tree.insert(&key, &key.repeat(64)), LeafInsertResult::Success);
    }

    // Most leaves now live only on disk. Corrupt the file so any read during drop would decode garbage pages.
    let length = std::fs::metadata(&path).unwrap().len();
    assert!(length > 8 * 1024 * 1024, "leaves must be evicted to disk, file is {length} bytes");
    std::fs::write(&path, vec![0u8; length as usize]).unwrap();

    drop(tree);
}
