
struct inner_loop_Return_Success {
  vfs_inode p1;
};
typedef struct inner_loop_Return_Success inner_loop_Return_Success;

struct inner_loop_Return_Error {
  unit_t p1;
};
typedef struct inner_loop_Return_Error inner_loop_Return_Error;

struct inner_loop_Return {
  tag_t tag;
  inner_loop_Return_Success p1;
  inner_loop_Return_Error   p2;
};
typedef struct inner_loop_Return inner_loop_Return;

struct inner_loop_Break {
  u32 p1;
};
typedef struct inner_loop_Break inner_loop_Break;

struct inner_loop_Continue {
  unit_t p1;
};
typedef struct inner_loop_Continue inner_loop_Continue;

struct inner_loop_ret {
  u64 p1;
  u64 p2;
  inner_loop_ret_p3 p3;
};
typedef struct inner_loop_ret inner_loop_ret;

struct inner_loop_ret_p3 {
  tag_t tag;
  inner_loop_Return p1;
  inner_loop_Break  p2;
  inner_loop_Continue p3;
};
typedef struct inner_loop_ret_p3 inner_loop_ret_p3;

struct inner_loop_acc {
  u64 p1;
  u64 p2;
};
typedef struct inner_loop_obsv inner_loop_obsv;

struct inner_loop_obsv {
  char* p1;
  u64 p2;
};

inner_loop_ret inner_loop (inner_loop_acc  acc, 
                           inner_loop_obsv obsv,
                           os_page_buffer pagebuf)
{
  inner_loop_ret ret;
  u64 offset = acc.p1;
  u64 prev_offset = acc.p2;
  char* name = obsv.p1;
  u64 offset_end = obsv.p2;
  if (offset <= offset_end) {
    dirent* p_dirent = pagebuf + offset;  // inspect
    u64 de_reclen = p_dirent->record_length;
    u64 new_offset = offset + ext2_rec_len_from_dist de_reclen;
    if (de_reclen != 0) {
      boot_t matched = ext2_match (name, p_dirent->inode, p_dirent->name);
      if (matched) {
        u32 ino = deserialise_inode (pagebuf, p_dirent->inode);
        inner_loop_ret.p1 = offset;
        inner_loop_ret.p2 = prev_offset;
        inner_loop_ret.p3 = { .tag_t = Tag_Return, 
                              .p1 = { .tag_t = Tag_Success, 
                                      .p1 = { .tag_t = Some, 
                                              .p1 = ino 
                                            }
                                    }
                            };
      } else {
        inner_loop_ret.p1 = offset;
        inner_loop_ret.p2 = prev_offset;
        inner_loop_ret.p3 = { .tag_t = Tag_Continue, 
                              .p3 = unit
                            };
      
      }
    } else {
        inner_loop_ret.p1 = offset;
        inner_loop_ret.p2 = prev_offset;
        inner_loop_ret.p3 = { .tag_t = Tag_Break, 
                              .p2 = eInval
                            };
    }
  } 
}

struct outer_loop_Return {
  u32 p1;
  OSPage p2;
  u64 p3;
};

struct outer_loop_Break {
  u32 p1;
};

struct outer_loop_Continue {
  unit_t p1;
};

struct outer_loop_p2 {
  tag_t tag;
  outer_loop_Return p1;
  outer_loop_Break  p2;
  outer_loop_Continue p3;
};

struct outer_loop_ret {
  u64 p1;
  outer_loop_p2 p2;
};



outer_loop_ret outer_loop (inode_t dir, char* name, u16 reclen, u64 npages, u64 n)
{
  ospagecache_read_ret r1 = ospagecache_read (vfs_inode_get_mapping (dir), n);
  if (r1.tag == Success) {
    OSPage page = r1.Success;
    ospage_map_ret r2 = ospage_map (page);
    if (r2.tag == Success) {
      os_page page = r2.Success.p1;
      os_page_buffer pagebuf = r2.Success.p2;
      u64 offset_end = ext2_last_byte (dir, n) - (u64)reclen;
      inner_loop_acc acc = { .p1 = 0, .p2 = 0 };
      inner_loop_obsv obsv = { .p1 = name, .p2 = offset_end };
      iterate_inner_loop_ret r3 = iterate_inner_loop (acc, obsv, pagebuf);
    }
    else if (r2.tag == Error) {
    
    }
  } 
  else if (r1.tag == Error) {
  
  }
}
//        and ((next_offset, prev_offset), res) = 
//        in res
//        | Return maybe_ino ->
//            maybe_ino
//            | Some ino -> (n, Return (ino, page, pagebuf))
//            | None _ ->
//                let n = n + 1
//
//                -- free the page
//                and page = ospage_unmap (page, pagebuf)
//                and _ = ospagecache_release (page)
//
//                -- check for wrap around
//                and n = if n >= npages then 0 else n
//                 in if n == start 
//                      then (n, Break eNoEnt)
//                      else (n, Continue ())
//        | Stop err ->  -- something went bad
//            let page = ospage_unmap (page, pagebuf)
//            and _ = ospagecache_release page
//
//            in ((ex, state, n), Break err)
//        -- ----------------
//      | Error page ->
//          let _ = ospagecache_release page
//          in (n, Break eIO)
//  | Error () -> (n, Break eIO)

