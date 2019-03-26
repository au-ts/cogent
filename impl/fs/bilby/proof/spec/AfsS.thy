(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory AfsS
imports
   "../lib/FunBucket"
   "../adt/VfsT"
   "../adt/WordArrayT"
   "../lib/CogentMonad"
begin

text {* High-level Correctness specification types *}

type_synonym byte = "U8"
type_synonym page = "U8 list"
type_synonym dir = "U8 list \<rightharpoonup> Ino"
type_synonym file_data = "page list"

datatype afs_inode_type =
  IDir "dir"
| IReg "file_data"
| ILnk  "U8 list"

definition "afs_inode_is_dir x \<equiv> \<exists>v. IDir v = x"
definition "afs_inode_is_reg x \<equiv> \<exists>v. IReg v = x"
definition "afs_inode_is_lnk x \<equiv> \<exists>v. ILnk v = x"

record afs_inode =
  i_type :: "afs_inode_type"
  i_ino :: "Ino"
  i_nlink :: "U32"
  i_size :: "U64"
  i_mtime :: "TimeT"
  i_ctime :: "TimeT"
  i_uid :: "U32"
  i_gid :: "U32"
  i_mode :: "Mode"
  i_flags :: "U32"

type_synonym readdir_ctx = "(U32 \<times> dir)" (* Remaining elements to read from the dir *)

type_synonym afs_map =  "Ino \<rightharpoonup> afs_inode" (* on-disk state *)

record afs_state =
  a_is_readonly :: "bool"
  a_current_time :: "TimeT"
  a_medium_afs :: "afs_map" (* On-medium FS observable when a crash happens or when sync fails before any update was applied *)
  a_medium_updates :: "(afs_map \<Rightarrow> afs_map) list" (* FIFO of on-medium updates *)

definition
  a_afs_updated_n :: "nat \<Rightarrow> afs_map \<Rightarrow> (afs_map \<Rightarrow> afs_map) list \<Rightarrow> afs_map"
where
 a_afs_updated_n_def[simp]:
 "a_afs_updated_n n afs_st updates = fold id (take n updates) afs_st"

definition
  a_afs_updated :: "afs_map \<Rightarrow> (afs_map \<Rightarrow> afs_map) list \<Rightarrow> afs_map"
where
 "a_afs_updated afs_st updates \<equiv> a_afs_updated_n (length updates) afs_st updates"

definition
  updated_afs :: "afs_state \<Rightarrow> afs_map"
where
  "updated_afs adata \<equiv> a_afs_updated (a_medium_afs adata) (a_medium_updates adata)"

abbreviation i_type_dir :: "afs_inode_type \<Rightarrow> dir"
 where
  "i_type_dir it \<equiv> (case it of IDir dir \<Rightarrow> dir)"

abbreviation i_dir :: "afs_inode \<Rightarrow> dir"
where
  "i_dir i \<equiv> i_type_dir (i_type i)"

definition
  i_dir_update :: "(dir \<Rightarrow> dir) \<Rightarrow> afs_inode \<Rightarrow> afs_inode"
 where
  i_dir_update_def[simp]:
  "i_dir_update m i \<equiv> i \<lparr>i_type:= IDir (m (i_dir i)) \<rparr>"
                                                  
abbreviation i_type_data :: "afs_inode_type \<Rightarrow> file_data"
where
  "i_type_data it \<equiv> (case it of IReg data \<Rightarrow> data)"
(*
abbreviation dirent_i_type :: "afs_inode_type \<Rightarrow> dirent_type"
where
 "dirent_i_type it \<equiv> (case it of IDir _ \<Rightarrow> DT_DIR | IReg _ \<Rightarrow> DT_REG | ILnk _ \<Rightarrow> DT_LNK)"
 *)
abbreviation i_data :: "afs_inode \<Rightarrow> file_data"
where
  "i_data i \<equiv> i_type_data (i_type i)"

abbreviation i_data_update :: "(file_data \<Rightarrow> file_data) \<Rightarrow> afs_inode \<Rightarrow> afs_inode"
 where
  "i_data_update m i \<equiv> i \<lparr>i_type:= IReg (m (i_data i)) \<rparr>"

abbreviation i_type_path :: "afs_inode_type \<Rightarrow> byte list"
where
  "i_type_path it \<equiv> (case it of ILnk path \<Rightarrow> path)"

abbreviation i_path :: "afs_inode \<Rightarrow> byte list"
where
  "i_path i \<equiv> i_type_path (i_type i)"

abbreviation i_path_update :: "(byte list \<Rightarrow> byte list) \<Rightarrow> afs_inode \<Rightarrow> afs_inode"
 where
  "i_path_update m i \<equiv> i \<lparr>i_type:= ILnk (m (i_path i)) \<rparr>"

primrec i_size_from_afs_inode_type :: "afs_inode_type \<Rightarrow> U64"
where
(* Can we prove anything about the size of a directory? *)
  "i_size_from_afs_inode_type (IDir dir) = undefined"
 |"i_size_from_afs_inode_type (IReg data) = count (concat data)"
 |"i_size_from_afs_inode_type (ILnk path) = count path"

abbreviation i_size_from_type :: "afs_inode \<Rightarrow> U64"
where
 "i_size_from_type i \<equiv> i_size_from_afs_inode_type $ i_type i"

definition
  afs_inode_to_vnode :: "afs_inode \<Rightarrow> VfsInode"
where
 "afs_inode_to_vnode i \<equiv> \<lparr>
    v_ino = i_ino i,
    v_nlink = i_nlink i,
    v_size =  i_size i,
    v_mtime = i_mtime i,
    v_ctime = i_ctime i,
    v_uid = i_uid i,
    v_gid = i_gid i,
    v_mode = i_mode i,
    v_flags = i_flags i\<rparr>"

definition
  afs_inode_from_vnode :: "vnode \<Rightarrow> afs_inode"
where
 "afs_inode_from_vnode v \<equiv> \<lparr>
    i_type = if (v_mode v AND s_IFREG \<noteq> 0) then IReg [] else if v_mode v AND s_IFDIR \<noteq> 0 then IDir Map.empty else ILnk [],
    i_ino = v_ino v,
    i_nlink = v_nlink v,
    i_size = v_size v,
    i_mtime = v_mtime v,
    i_ctime = v_ctime v,
    i_uid = v_uid v,
    i_gid = v_gid v,
    i_mode = v_mode v,
    i_flags = v_flags v\<rparr>"

definition
  error_if_readonly :: "afs_state \<Rightarrow> (((ErrCode \<times> afs_state), afs_state) R) cogent_monad"
where
  "error_if_readonly as \<equiv> return $ if a_is_readonly as then Error (eRoFs, as) else Success as"

definition
  nondet_error :: "ErrCode set \<Rightarrow> (ErrCode \<Rightarrow> 'a) \<Rightarrow> 'a cogent_monad"
where
  "nondet_error errs f \<equiv> CogentMonad.select errs >>= (return o f)"

text {*
 @{term afs_alloc_inum}: We ensure that it only returns inums not already in used
 (by checking it is in the set @{text "-dom as"}). The function can
  return an Error.
*} 
definition
  afs_alloc_inum :: "afs_map \<Rightarrow> ((unit, Ino) R) cogent_monad"
where
 "afs_alloc_inum as \<equiv>
    (do
     avail_inums \<leftarrow> return $ - dom as ;
     opt_inum \<leftarrow> select $ {option.None} \<union> option.Some ` avail_inums ;
     return $ if opt_inum = option.None then
        Error ()
      else        
        Success (the opt_inum)
     od)"


(* os_get_current_time *)
definition
 afs_get_current_time :: "afs_state \<Rightarrow> (afs_state \<times> TimeT) cogent_monad"
where
 "afs_get_current_time afs \<equiv> do
   time' \<leftarrow> return (a_current_time afs);
   time \<leftarrow> select {x. x \<ge> time'};
   return (afs\<lparr> a_current_time := time \<rparr>, time')
  od"


definition
  afs_init_inode :: "afs_state \<Rightarrow> vnode \<Rightarrow> vnode \<Rightarrow> VfsMode \<Rightarrow>
                      ((afs_state \<times> vnode, afs_state \<times> vnode) R) cogent_monad"
where
 "afs_init_inode adata vdir vnode mode \<equiv> do
     (adata, time) \<leftarrow> afs_get_current_time adata;
     uid \<leftarrow> return (v_uid vdir);
     gid \<leftarrow> return (v_gid vdir);
     vnode \<leftarrow> return (vnode\<lparr> v_ctime:=time, v_mtime:=time, v_uid:=uid,
                         v_gid:=gid, v_mode:=mode, v_nlink:=1, v_size:=0 \<rparr>);
     r \<leftarrow> afs_alloc_inum (updated_afs adata);
     return (case r of
       Error () \<Rightarrow> Error (adata, vnode)
       | Success inum \<Rightarrow> Success (adata, vnode\<lparr> v_ino := inum \<rparr>)
      )
  od"

definition
  read_afs_inode :: "afs_state \<Rightarrow> Ino \<Rightarrow> ((afs_inode,ErrCode) R\<^sub>T) cogent_monad"
where
 "read_afs_inode adata ino \<equiv>
   return (Success $ the $ updated_afs adata ino) \<sqinter>
     nondet_error {eIO, eNoMem, eInval, eBadF} Error"

definition
 afs_apply_updates_nondet :: "afs_state \<Rightarrow> afs_state cogent_monad"
where
 "afs_apply_updates_nondet afs  \<equiv> do
    (to_apply, updates) \<leftarrow> {(ap, up). ap @ up = a_medium_updates afs};
    return (afs \<lparr>a_medium_afs := fold id to_apply  (a_medium_afs afs),
                 a_medium_updates := updates\<rparr>)
  od"

definition
 afs_update :: "afs_state \<Rightarrow> (afs_map \<Rightarrow> afs_map) \<Rightarrow> (afs_state \<times> (unit, ErrCode)  R\<^sub>T) cogent_monad"
where
 "afs_update afs upd \<equiv> do
    afs \<leftarrow> afs_apply_updates_nondet (afs\<lparr>a_medium_updates := a_medium_updates afs @ [upd]\<rparr>) ;
    if a_medium_updates afs  = [] then 
      return (afs, Success ())
    else
      return (afs, Success ()) \<sqinter>
      nondet_error {eIO, eNoSpc, eNoMem} (\<lambda>e. (afs\<lparr>a_medium_updates:= butlast (a_medium_updates afs)\<rparr>,Error e))
  od"

definition
  afs_create :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> VfsMode \<Rightarrow> vnode \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_create afs parentdir name mode vnode \<equiv>
  if a_is_readonly afs then
    return ((afs, parentdir, vnode), Error eRoFs)
   else do
   r \<leftarrow> afs_init_inode afs parentdir vnode  (mode OR s_IFREG) ;
   case r of
     Error (afs, vnode) \<Rightarrow> return ((afs, parentdir, vnode), Error eNFile)
   | Success (afs, vnode) \<Rightarrow> do
   r \<leftarrow> read_afs_inode afs (v_ino parentdir);
   case r of
      Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
    | Success dir \<Rightarrow> do
     r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa name \<mapsto> v_ino vnode)) dir) \<sqinter> return (Error eNameTooLong);
     case r of
       Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
     | Success dir \<Rightarrow> do
   r \<leftarrow> select (Success ` {sz. sz > v_size parentdir }) \<sqinter> (return (Error eOverflow));
   case r of
     Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
    | Success newsz \<Rightarrow> do
   time \<leftarrow> return (v_ctime vnode);
   dir \<leftarrow> return (dir\<lparr>i_ctime:=time, i_mtime:=time\<rparr>);
   inode  \<leftarrow> return (afs_inode_from_vnode vnode);
   (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino inode \<mapsto> inode, i_ino dir \<mapsto> dir));
   case r of
     Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
   | Success () \<Rightarrow>
      return ((afs, parentdir \<lparr> v_ctime := time, v_mtime := time, v_size := newsz \<rparr>, vnode), Success ())
      od
     od
    od
   od
 od"

text {* Sync can return an error non-deterministicaly. The only restriction
is that @{term afs_sync} can only return successfully if the list of updates is
empty. As the user expects, when calling sync all the updates related to an
inode should be synchronised to disk.
*}
definition
  afs_sync :: "afs_state \<Rightarrow> (afs_state \<times> (unit,ErrCode) R\<^sub>T) cogent_monad"
where
"afs_sync afs \<equiv>
  if a_is_readonly afs then
    return (afs, Error eRoFs)
  else do
    n \<leftarrow> select {0..length (a_medium_updates afs)};
    let updates = a_medium_updates afs;
        (to_apply, updates) = (take n updates,drop n updates);
        afs = a_medium_afs_update (fold (\<lambda>upd med. upd med) to_apply) afs;
        afs = a_medium_updates_update (\<lambda>_. updates) afs
    in if updates = [] then
      return (afs, Success ())
    else do
      e \<leftarrow> select {eIO, eNoMem, eNoSpc,eOverflow};
      return (afs\<lparr>a_is_readonly:= (e = eIO)\<rparr>, Error e)
    od
  od" 

(* Assumptions:  "v_ino parentdir \<in> dom (a_medium_afs (a_afs_updated afs))" 
                In other words, the v_inode for the parent dir must be represented in the afs data structure.
  nlinks of vnode < MaxWord -1
 *)

definition
  afs_unlink :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_unlink afs parentdir name vnode \<equiv>
    do
     r \<leftarrow> error_if_readonly afs;
     case r of
       Error (e, afs) \<Rightarrow> return ((afs, parentdir, vnode), Error e)
     | Success afs \<Rightarrow> do
     (afs, time) \<leftarrow> afs_get_current_time afs;
     (* We need to use updated afs because inode might contain data blocks *)
     inode  \<leftarrow> return ((the $ updated_afs afs (v_ino vnode))\<lparr>i_nlink:= v_nlink vnode - 1, i_ctime:= time\<rparr>) ;
     newsize \<leftarrow> select {sz. sz < v_size parentdir};
     dir_ino \<leftarrow> return (v_ino parentdir);
     (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(dir_ino \<mapsto> (i_dir_update (\<lambda>d. d(\<alpha>wa name:=option.None)) (the $ f dir_ino)\<lparr>i_ctime:=time,i_mtime:=time\<rparr>),
                                            v_ino vnode \<mapsto> inode));
       case r of
         Error e \<Rightarrow>
          return ((afs, parentdir, vnode), Error e)
       | Success () \<Rightarrow>
         let vnode' = vnode \<lparr> v_nlink := v_nlink vnode - 1, v_ctime:= time\<rparr>;
             parentdir' = parentdir \<lparr> v_ctime := time, v_mtime := time, v_size := newsize \<rparr>
         in return ((afs, parentdir', vnode'), Success ())
     od
  od"

definition
  afs_iget :: "afs_state \<Rightarrow> Ino \<Rightarrow> vnode \<Rightarrow> (vnode \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
 "afs_iget afs inum vnode \<equiv>
  (if inum \<in> dom (updated_afs afs) then
    do
      r \<leftarrow> read_afs_inode afs inum;
      case r of
       Success inode \<Rightarrow>
        (* update vnode with inode *)
        return (afs_inode_to_vnode inode, Success ())
      | Error e \<Rightarrow>
       return (vnode, Error e)
    od
  else return (vnode, Error eNoEnt))
  "

definition
  afs_lookup :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> ((Ino, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_lookup afs vdir name \<equiv>
   if wordarray_length name > bilbyFsMaxNameLen + 1 then
     return (Error eNameTooLong)
   else
   do
      r \<leftarrow> read_afs_inode afs (v_ino vdir);
   case r of
      Error e \<Rightarrow> return (Error e)
    | Success dir \<Rightarrow>
      (case i_dir dir (\<alpha>wa name) of
         None \<Rightarrow> return (Error eNoEnt)
       | Some ino \<Rightarrow> return (Success ino))
    od"

definition
  afs_link :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_link afs parentdir name vnode \<equiv>
  if a_is_readonly afs then
    return ((afs, parentdir, vnode), Error eRoFs)
   else do
   r \<leftarrow> read_afs_inode afs (v_ino parentdir);
   case r of
      Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
    | Success dir \<Rightarrow> do
     r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa name \<mapsto> v_ino vnode)) dir) \<sqinter> return (Error eNameTooLong);
     case r of
       Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
     | Success dir \<Rightarrow> do
   r \<leftarrow> select (Success ` {sz. sz > v_size parentdir }) \<sqinter> (return (Error eOverflow));
   case r of
     Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
    | Success newsz \<Rightarrow> do
   time \<leftarrow> return (v_ctime vnode);
   dir \<leftarrow> return (dir\<lparr>i_ctime:=time, i_mtime:=time, i_size := newsz\<rparr>);
   (* We need to use updated_afs because vnode might contain data blocks *)
   inode  \<leftarrow> return (the $ updated_afs afs (v_ino vnode));
   (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino inode \<mapsto> inode, i_ino dir \<mapsto> dir));
   case r of
     Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
   | Success () \<Rightarrow>
      return ((afs, parentdir \<lparr> v_ctime := time, v_mtime := time, v_size := newsz \<rparr>, vnode \<lparr>v_nlink:= v_nlink vnode + 1\<rparr>), Success ())
      od
     od
    od
   od"

definition
  afs_mkdir :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> VfsMode \<Rightarrow> vnode \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_mkdir afs parentdir name mode vnode \<equiv>
  if a_is_readonly afs then
    return ((afs, parentdir, vnode), Error eRoFs)
   else do
   r \<leftarrow> afs_init_inode afs parentdir vnode  (mode OR s_IFDIR) ;
   case r of
     Error (afs, vnode) \<Rightarrow> return ((afs, parentdir, vnode), Error eNFile)
   | Success (afs, vnode) \<Rightarrow> do
   r \<leftarrow> read_afs_inode afs (v_ino parentdir);
   case r of
      Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
    | Success dir \<Rightarrow> do
     r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa name \<mapsto> v_ino vnode)) dir) \<sqinter> return (Error eNameTooLong);
     case r of
       Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
     | Success dir \<Rightarrow> do
   r \<leftarrow> select (Success ` {sz. sz > v_size parentdir }) \<sqinter> (return (Error eOverflow));
   case r of
     Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
    | Success newsz \<Rightarrow>
  do
   time \<leftarrow> return (v_ctime vnode);
   dir \<leftarrow> return (dir\<lparr>i_ctime:=time, i_mtime:=time, i_nlink := i_nlink dir + 1, i_size := newsz\<rparr>);
   vnode \<leftarrow> return (vnode \<lparr> v_nlink := 2\<rparr>);
   inode  \<leftarrow> return (afs_inode_from_vnode vnode);
   (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino inode \<mapsto> inode, i_ino dir \<mapsto> dir));
   case r of
     Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
   | Success () \<Rightarrow>
      return ((afs, parentdir \<lparr>v_nlink:= v_nlink parentdir + 1, v_ctime := time, v_mtime := time, v_size := newsz \<rparr>, vnode), Success ())
      od
     od
    od
   od
 od"

definition
  afs_rmdir :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_rmdir afs parentdir name vnode \<equiv>
    do
     r \<leftarrow> error_if_readonly afs;
     case r of
       Error (e, afs) \<Rightarrow> return ((afs, parentdir, vnode), Error e)
     | Success afs \<Rightarrow> 
     if dom (i_dir (the $ updated_afs afs (v_ino vnode))) \<noteq> {} then
       return ((afs, parentdir, vnode), Error eNotEmpty)
     else
     do
     (afs, time) \<leftarrow> afs_get_current_time afs;
     vnode' \<leftarrow> return (vnode \<lparr> v_nlink := 0 \<rparr>);
     (* no need to use updated afs since vnode must be an empty dir *)
     inode  \<leftarrow> return (afs_inode_from_vnode vnode);
     newsize \<leftarrow> select {sz. sz < v_size parentdir};
     dir_ino \<leftarrow> return (v_ino parentdir);
     parentdir' \<leftarrow> return (parentdir \<lparr> v_nlink := v_nlink parentdir - 1, v_ctime := time, v_mtime := time, v_size := newsize \<rparr>);
     (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(dir_ino \<mapsto> (i_dir_update (\<lambda>d. d(\<alpha>wa name:=option.None)) (the $ f dir_ino)\<lparr>i_ctime:=time,i_mtime:=time, i_nlink:= v_nlink parentdir'\<rparr>),
                                            v_ino vnode \<mapsto> inode));
       case r of
         Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
       | Success () \<Rightarrow>
         return ((afs, parentdir', vnode'), Success ())
     od
  od"

definition
  afs_symlink :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> U8 WordArray \<Rightarrow> VfsMode \<Rightarrow> vnode \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_symlink afs parentdir name symname mode vnode \<equiv>
  if a_is_readonly afs then
    return ((afs, parentdir, vnode), Error eRoFs)
  else if wordarray_length symname > bilbyFsBlockSize then
     return ((afs, parentdir, vnode), Error eNameTooLong)
   else do
   r \<leftarrow> afs_init_inode afs parentdir vnode  (mode OR s_IFLNK OR s_IRWXUGO) ;
   case r of
     Error (afs, vnode) \<Rightarrow> return ((afs, parentdir, vnode), Error eNFile)
   | Success (afs, vnode) \<Rightarrow> do
   r \<leftarrow> read_afs_inode afs (v_ino parentdir);
   case r of
      Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
    | Success dir \<Rightarrow> do
     r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa name \<mapsto> v_ino vnode)) dir) \<sqinter> return (Error eNameTooLong);
     case r of
       Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
     | Success dir \<Rightarrow> do
   r \<leftarrow> select (Success ` {sz. sz > v_size parentdir }) \<sqinter> (return (Error eOverflow));
   case r of
     Error e \<Rightarrow>  return ((afs, parentdir, vnode), Error e)
    | Success newsz \<Rightarrow> do
   time \<leftarrow> return (v_ctime vnode);
   vnode \<leftarrow> return (vnode \<lparr> v_size := ucast $ wordarray_length symname \<rparr>);
   dir \<leftarrow> return (dir\<lparr>i_ctime:=time, i_mtime:=time, i_size := v_size vnode\<rparr>);
   inode \<leftarrow> return (afs_inode_from_vnode vnode);
   inode \<leftarrow> return (i_path_update (\<lambda>_. \<alpha>wa symname) inode);
   (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino inode \<mapsto> inode, i_ino dir \<mapsto> dir));
   case r of
     Error e \<Rightarrow> return ((afs, parentdir, vnode), Error e)
   | Success () \<Rightarrow>
      return ((afs, parentdir \<lparr> v_ctime := time, v_mtime := time, v_size := newsz \<rparr>, vnode), Success ())
      od
     od
    od
   od
 od"

definition
  pad_block :: "U8 list \<Rightarrow> U32 \<Rightarrow> U8 list"
where
 "pad_block data len \<equiv> data @ drop (length data) (replicate (unat len) 0)"

(* No support for holes for now *)

definition
  afs_readpage :: "afs_state \<Rightarrow> vnode \<Rightarrow> U64 \<Rightarrow> U8 WordArray \<Rightarrow>
                   ((afs_state \<times> vnode \<times> U8 WordArray) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_readpage afs vnode block buf \<equiv>
   if block > (v_size vnode >> unat bilbyFsBlockShift) then
    return ((afs, vnode, WordArrayT.make (replicate (unat bilbyFsBlockSize) 0)), Error eNoEnt)
   else if (block = (v_size vnode >> unat bilbyFsBlockShift)) \<and> ((v_size vnode) mod (ucast bilbyFsBlockSize) = 0)
        then return ((afs, vnode, buf), Success ())
        else do
          err \<leftarrow> {eIO, eNoMem, eInval, eBadF, eNoEnt};
          return ((afs, vnode, WordArrayT.make (pad_block ((i_data (the $ updated_afs afs (v_ino vnode))) ! unat block) bilbyFsBlockSize)), Success ()) \<sqinter> return ((afs, vnode, buf), Error err)
          od
"

definition
  afs_write_begin :: "afs_state \<Rightarrow> vnode \<Rightarrow> U64 \<Rightarrow> U32 \<Rightarrow> U8 WordArray \<Rightarrow>
                   ((afs_state \<times> vnode \<times> U8 WordArray) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_write_begin afs vnode pos len buf \<equiv>
  if a_is_readonly afs then
    return ((afs, vnode, buf), Error eRoFs)
  else 
    do
     ((afs, vnode, buf'), r) \<leftarrow> afs_readpage afs vnode (pos >> unat bilbyFsBlockShift) buf;
    case r of
      Error e \<Rightarrow> 
      return ((afs, vnode, buf'), if e = eNoEnt then Success () else Error e)
    | Success () \<Rightarrow>
      return ((afs, vnode, buf'), Success())
    od
"

definition
  afs_write_end :: "afs_state \<Rightarrow> vnode \<Rightarrow> U64 \<Rightarrow> U32 \<Rightarrow> U8 WordArray \<Rightarrow>
                   ((afs_state \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_write_end afs vnode pos len addr \<equiv>
  if a_is_readonly afs then
    return ((afs, vnode), Error eRoFs)
  else 
    do
      newsize \<leftarrow> return (max (v_size vnode) (pos + ucast len));
      (afs, time) \<leftarrow> afs_get_current_time afs;
      vnode' \<leftarrow> return (vnode \<lparr> v_size:= newsize, v_mtime := time\<rparr>);
      block \<leftarrow> return (unat $ pos >> unat bilbyFsBlockShift);
      (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(v_ino vnode \<mapsto> i_data_update (\<lambda>data. data[block:= \<alpha>wa addr]) (the $ f (v_ino vnode)) \<lparr> i_size:= newsize \<rparr>));
       case r of
         Error e \<Rightarrow> return ((afs, vnode), Error e)
       | Success () \<Rightarrow>
         return ((afs, vnode'), Success())
    od
"

definition
  afs_evict_inode :: "afs_state \<Rightarrow> vnode \<Rightarrow>
                   (afs_state \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_evict_inode afs vnode \<equiv>
  if a_is_readonly afs then
    return (afs, Error eRoFs)
  else 
    if v_nlink vnode \<noteq> 0 then
      return (afs, Success ())
    else 
     afs_update afs (\<lambda>f. f(v_ino vnode:= None))
"

definition
  afs_follow_link :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow>
                   ((afs_state \<times> vnode \<times> U8 WordArray) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_follow_link afs vnode path \<equiv>
  do
   r \<leftarrow> read_afs_inode afs (v_ino vnode);
   case r of
    Error e \<Rightarrow>
     return ((afs, vnode, path), Error e)
   | Success inode \<Rightarrow>
     let wa_path = WordArrayT.make (i_path inode);
         updated_path = wordarray_copy (path, wa_path, 0, 0, ucast (i_size inode))
     in return ((afs, vnode, updated_path), Success ())
   od
"

definition
  afs_rename :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode option \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode \<times> vnode option) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_rename afs vdir oldname oldvnode newname onewvnode \<equiv>
  if a_is_readonly afs then
    return ((afs, vdir, oldvnode, onewvnode), Error eRoFs)
  else do
    old_is_dir \<leftarrow> return ( S_ISDIR (v_mode oldvnode));
    ncnt \<leftarrow> return (if old_is_dir then v_nlink oldvnode - 1 else v_nlink oldvnode);
    oldvnode' \<leftarrow> return (oldvnode \<lparr> v_nlink := ncnt \<rparr>);
    oldinode  \<leftarrow> return ((the $ updated_afs afs (v_ino oldvnode))\<lparr> i_nlink := ncnt \<rparr>);
    (afs, time) \<leftarrow> afs_get_current_time afs;
    newsz \<leftarrow> select UNIV;
    r \<leftarrow> read_afs_inode afs (v_ino vdir);
    case r of
    Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)    
    | Success dir \<Rightarrow> do
    r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa oldname := None, 
                    \<alpha>wa newname := Some (v_ino oldvnode) )) dir) \<sqinter> return (Error eNameTooLong);
    case r of
     Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)
    | Success dir \<Rightarrow> do
    dir \<leftarrow> return (dir\<lparr>i_ctime:=time, i_mtime:=time, i_size := newsz\<rparr>);   
    (case onewvnode of
    Some newvnode \<Rightarrow>
     let newinode = the $ updated_afs afs (v_ino newvnode);
         new_is_dir = afs_inode_is_dir (i_type newinode) 
     in if new_is_dir \<and> dom (i_dir newinode) \<noteq> {} then
         return ((afs, vdir, oldvnode, onewvnode), Error eNotEmpty)
      else
        do
         ncnt \<leftarrow> return (if new_is_dir then 0 else v_nlink newvnode - 1);
         newvnode' \<leftarrow> return (newvnode \<lparr> v_nlink := ncnt \<rparr>);
         newinode \<leftarrow> return (newinode \<lparr> i_nlink := ncnt \<rparr>);
         (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino oldinode \<mapsto> oldinode, i_ino dir \<mapsto> dir,
                                           i_ino newinode \<mapsto> newinode));
         case r of
           Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)
         | Success () \<Rightarrow>
           let vdir' = vdir \<lparr> v_mtime := time, v_ctime := time, v_size := newsz \<rparr>
           in return ((afs, vdir', oldvnode', Some newvnode'), Success ())
       od
      | None \<Rightarrow>
        do
         (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino oldinode \<mapsto> oldinode, i_ino dir \<mapsto> dir));
         case r of
           Error e \<Rightarrow> return ((afs, vdir, oldvnode, onewvnode), Error e)
         | Success () \<Rightarrow>
           let vdir' = vdir \<lparr> v_mtime := time, v_ctime := time, v_size := newsz \<rparr>
           in return ((afs, vdir', oldvnode', None), Success ())
        od)
     od
  od
od
"

definition
  afs_move :: "afs_state \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode \<Rightarrow> vnode \<Rightarrow> U8 WordArray \<Rightarrow> vnode option \<Rightarrow>
                   ((afs_state \<times> vnode \<times> vnode \<times> vnode \<times> vnode option) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_move afs oldvdir oldname oldvnode newvdir newname onewvnode \<equiv>
  if a_is_readonly afs then
    return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error eRoFs)
  else do
    old_is_dir \<leftarrow> return (S_ISDIR (v_mode oldvnode));
    ncnt \<leftarrow> return (if old_is_dir then v_nlink oldvnode - 1 else v_nlink oldvnode);
    oldvnode' \<leftarrow> return (oldvnode \<lparr> v_nlink := ncnt \<rparr>);
    oldinode  \<leftarrow> return ((the $ updated_afs afs (v_ino oldvnode))\<lparr> i_nlink := ncnt \<rparr>);
    (afs, time) \<leftarrow> afs_get_current_time afs;
    r \<leftarrow> read_afs_inode afs (v_ino oldvdir);
    case r of
    Error e \<Rightarrow> return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)    
    | Success olddir \<Rightarrow> do
    r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa oldname := None,
                    \<alpha>wa newname := Some (v_ino oldvnode) )) olddir) \<sqinter> return (Error eNameTooLong);
    case r of
     Error e \<Rightarrow> return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
    | Success olddir \<Rightarrow> do
    onewsz \<leftarrow> select {sz. sz < v_size oldvdir};
    olddir \<leftarrow> return (olddir\<lparr>i_ctime:=time, i_mtime:=time, i_size := onewsz\<rparr>);   
    oldvdir' \<leftarrow> return (oldvdir \<lparr> v_mtime := time, v_ctime := time, v_size := onewsz \<rparr>);

    r \<leftarrow> read_afs_inode afs (v_ino newvdir);
    case r of
    Error e \<Rightarrow> return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)    
    | Success newdir \<Rightarrow> do
    r  \<leftarrow> return (Success $ i_dir_update (\<lambda>d. d(\<alpha>wa newname := Some (v_ino oldvnode) )) newdir)
          \<sqinter> return (Error eNameTooLong);
    case r of
     Error e \<Rightarrow> return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
    | Success newdir \<Rightarrow> do
    nnewsz \<leftarrow> select {sz. sz > v_size newvdir};

    ncnt \<leftarrow> return (if old_is_dir then v_nlink newvdir + 1 else v_nlink newvdir);
    newvdir' \<leftarrow> return (newvdir \<lparr>v_ctime:=time, v_mtime:=time, v_nlink := ncnt, v_size := nnewsz \<rparr>);
    newdir \<leftarrow> return (newdir\<lparr>i_ctime:=time, i_mtime:=time, i_nlink := ncnt, i_size := nnewsz\<rparr>);

    (case onewvnode of
    Some newvnode \<Rightarrow>
     let newinode = the $ updated_afs afs (v_ino newvnode);
         new_is_dir = afs_inode_is_dir (i_type newinode) 
     in if new_is_dir \<and> dom (i_dir newinode) \<noteq> {} then
         return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error eNotEmpty)
      else
        do
         ncnt \<leftarrow> return (if new_is_dir then 0 else v_nlink newvnode - 1);
         newvnode' \<leftarrow> return (newvnode \<lparr> v_nlink := ncnt \<rparr>);
         newinode \<leftarrow> return (newinode \<lparr> i_nlink := ncnt \<rparr>);


         (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino oldinode \<mapsto> oldinode, i_ino olddir \<mapsto> olddir,
                                           i_ino newdir \<mapsto> newdir, i_ino newinode \<mapsto> newinode));
         case r of
           Error e \<Rightarrow> return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
         | Success () \<Rightarrow>
           return ((afs, oldvdir', oldvnode', newvdir', Some newvnode'), Success ())
       od
      | None \<Rightarrow>
        do
         (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(i_ino oldinode \<mapsto> oldinode, i_ino olddir \<mapsto> olddir,
                                           i_ino newdir \<mapsto> newdir));
         case r of
           Error e \<Rightarrow> return ((afs, oldvdir, oldvnode, newvdir, onewvnode), Error e)
         | Success () \<Rightarrow>
           return ((afs, oldvdir', oldvnode', newvdir', None), Success ())
        od)
      od
    od
    od
    od
  od"

definition
  afs_dir_emit :: "readdir_ctx \<Rightarrow> U8 WordArray \<Rightarrow> Ino \<Rightarrow> VfsType  \<Rightarrow> ((readdir_ctx, readdir_ctx) LoopResult\<^sub>T) cogent_monad"
where
 "afs_dir_emit \<equiv> (\<lambda>(pos, entries) name ino vtype.
  do bool \<leftarrow> select UNIV;
    if bool then
      return (Iterate (pos, entries(\<alpha>wa name:= None)))
    else
      return (Break (pos, entries (\<alpha>wa name:= None)))
  od)
 "
(* VFS detects when readdir is called twice without removing
any entry from the readdir context. *)
definition
  afs_readdir :: "afs_state \<Rightarrow> readdir_ctx \<Rightarrow> BilbyFsReaddirContext\<^sub>T option \<Rightarrow> vnode \<Rightarrow> ((afs_state \<times> readdir_ctx \<times> BilbyFsReaddirContext\<^sub>T option) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_readdir afs rdctx obrdctx vdir =
    do
     r \<leftarrow> read_afs_inode afs (v_ino vdir);
     case r of
      Error e \<Rightarrow> return ((afs, rdctx, obrdctx), Error e)  
     | Success dir \<Rightarrow> do
      toemit \<leftarrow> select {entries. entries \<subseteq> dom (i_dir dir) };
      obrdctx \<leftarrow> select UNIV;
      pos \<leftarrow> select UNIV;
      return ((afs, (pos, (snd rdctx)|`(-toemit)), obrdctx),
                Success ())
    od
  od"

record vfsstat =
  vs_ino :: Ino
  vs_nlink :: U32
  vs_mode :: Mode
  vs_uid :: U32
  vs_gid :: U32
  vs_size :: U64
  vs_atime :: TimeT 
  vs_mtime :: TimeT
  vs_ctime :: TimeT
  vs_blksize :: U32
  vs_blocks :: U32

definition
  afs_getattr :: "afs_state \<Rightarrow> vfsstat \<Rightarrow> vnode \<Rightarrow> ((afs_state \<times> vfsstat)) cogent_monad"
where                                
  "afs_getattr afs stat vnode \<equiv>
   return (afs, stat
    \<lparr> vs_ino := v_ino vnode,
      vs_nlink := v_nlink vnode,
      vs_mode := v_mode vnode,
      vs_uid := v_uid vnode,
      vs_gid := v_gid vnode,
      vs_size := v_size vnode,
      vs_atime := v_mtime vnode,
      vs_mtime := v_mtime vnode,
      vs_ctime := v_ctime vnode,
      vs_blksize := bilbyFsBlockSize,
      vs_blocks := ucast (v_size vnode) div 512 + (if v_size vnode mod 512 > 0 then 1 else 0)
    \<rparr>)
    "

record iattr =
 iattr_valid :: U32
 iattr_mode :: Mode
 iattr_uid :: U32
 iattr_gid :: U32
 iattr_mtime :: TimeT
 iattr_ctime :: TimeT

definition iattr_is_set :: "iattr \<Rightarrow> U32 \<Rightarrow> bool"
where
 "iattr_is_set iattr flag \<equiv> iattr_valid iattr AND flag \<noteq> 0"
 
definition
  afs_setattr :: "afs_state \<Rightarrow> iattr \<Rightarrow> vnode \<Rightarrow> ((afs_state \<times> vnode) \<times> (unit, ErrCode) R\<^sub>T) cogent_monad"
where
  "afs_setattr afs iattr vnode \<equiv> 
  let 
    vnode' = (if iattr_is_set iattr vfs_ATTR_MODE then vnode \<lparr> v_mode := iattr_mode iattr \<rparr> else vnode);
    vnode' = (if iattr_is_set iattr vfs_ATTR_UID then vnode' \<lparr> v_uid := iattr_uid iattr \<rparr> else vnode');
    vnode' = (if iattr_is_set iattr vfs_ATTR_GID then vnode' \<lparr> v_gid := iattr_gid iattr \<rparr> else vnode');
    vnode' = (if iattr_is_set iattr vfs_ATTR_MTIME then vnode' \<lparr> v_mtime := iattr_mtime iattr \<rparr> else vnode');
    vnode' = (if iattr_is_set iattr vfs_ATTR_CTIME then vnode' \<lparr> v_ctime := iattr_ctime iattr \<rparr> else vnode')
  in do
    (afs, r) \<leftarrow> afs_update afs (\<lambda>f. f(v_ino vnode' \<mapsto>
      the (f(v_ino vnode'))\<lparr>i_mode:= v_mode vnode', i_uid := v_uid vnode', i_gid := v_gid vnode',
         i_mtime := v_mtime vnode', i_ctime := v_ctime vnode'\<rparr>));
    case r of
      Error e \<Rightarrow> return ((afs, vnode), Error e)
    | Success () \<Rightarrow>
      return ((afs, vnode'), Success())
   od"

end
