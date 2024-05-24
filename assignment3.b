import "util"
import "iosb"
import "heap"

 
 
let error_names = table "NONE", "BADCODE", "READPARAMS", "DEVNUMBER", "POSITION", "MEMORY",
                        "DEVFAILED", "NOTFOUND", "BADPARAM", "INUSE", "CANTCREATE", "NODATA",
                        "SOFTWARE";
 
 
manifest {
  last_error = -12;
  superblock_pos = 0;
 
  //superblock indexes
  list.first = 0;
  list.last = 1;
  list.pointer = 2;
  free.blocks = 3;
  rootdir.index = 4;
  sb_firstfreeblock = 5;
  sb_datetime = 6;
  sb_name = 7;
  sb_name_lengthwords = 8;
  sb_size = 9;
 
  //directory entry indexes
  de_name = 0;
  de_name_lengthwords = 3;
  de_length = 3;
  de_blocknum = 3;
  sizeof_de = 4;
  max_num_de = 128 / sizeof_de,
 
  //header block indexes
  hb_length_byte = 0;
  hb_length_block = 1;
  hb_createtime = 2;
  hb_modtime = 3;
  hb_fileinfo = 4;
  hb_perm = 5;
  hb_startblock = 6;
  hb_buff = 7;
  hb_buff_pos = 8;
  hb_block = 9;
  hb_curr_wblk = 10;
  hb_file_level = 11;
 
 
  iosb_dirent = iosb_extra_1;
  iosb_bufferblock = iosb_extra_2;
  iosb_headerblock = iosb_extra_3 }
 
let command_loop = nil;
let error_reason = nil;
 
let sizes = vec(10);
let rootdir = vec(128);
let superblock = vec(128);
let window = vec(256);
let headerblock = vec(128);
let disc_mounted = false;
let total_blocks = 0;
let list_blocks = 0;
let window.pointer = 0;
let leftwindow = 1;
let rightwindow = 2;
 
let perror(code, message1, message2) be
{ test code >= 0 then
  { emergency_outs("\nNot an error, code");
    emergency_outno(code) }
  or test code = EOF then
    emergency_outs("\nEnd of file")
  or test code < last_error then
  { emergency_outs("\nUnrecognised error code ");
    emergency_outno(code) }
  or
  { emergency_outs("\nError code ");
    emergency_outno(code);
    emergency_outch(' ');
    emergency_outs(error_names ! - code) }
  emergency_outs(", ");
  emergency_outs(message1);
  emergency_outch(' ');
  emergency_outs(message2);
  emergency_outch('\n');
  if error_reason <> nil then
  { emergency_outs("reason: ");
    emergency_outs(error_reason);
    error_reason := nil;
    emergency_outch('\n') } }
 
 
let equals(a, b) be
{ let i = 0;
  while true do
  { let ca = byte i of a, cb = byte i of b;
    if ca <> cb then
      resultis false;
    if ca = 0 then
      resultis true;
    i +:= 1 } }
 
let begins_with(a, b) be
{ let i = 0;
  while true do
  { let ca = byte i of a, cb = byte i of b;
    if ca <> cb then
      resultis cb = 0;
    if ca = 0 then
      resultis true;
    i +:= 1 } }
 
let equals_after(a, skip, b) be
{ let i = 0, j = 0;
  while i < skip do
  { if byte i of a = 0 then
      resultis false;
    i +:= 1 }
  while true do
  { let ca = byte i of a, cb = byte j of b;
    if ca <> cb then
      resultis false;
    if ca = 0 then
      resultis true;
    i +:= 1;
    j +:= 1 } }
 
let skip_chars_in(num, str) be
{ let i = 0, j = 0, c;
  while i < num do
  { c := byte i of str;
    if c = 0 then
    { byte 0 of str := 0;
      return }
    i +:= 1 }
  while true do
  { c := byte i of str;
    byte j of str := c;
    if c = 0 then
      return;
    i +:= 1;
    j +:= 1 } }
 
let strcpy_n_to_n(a, wordsa, b) be                  // normal to normal
{ let maxa = wordsa * 4 - 2, idx = 0, c;
  while idx <= maxa do
  { c := byte idx of b;
    if c = 0 then
      break;
    byte idx of a := c;
    idx +:= 1 }
  byte idx of a := 0 }
 
let strcpy_f_to_f(a, wordsa, b, wordsb) be          // fixed to fixed
{ let maxa = wordsa * 4 - 1, maxb = wordsb * 4 - 1, idx = 0, c;
  while idx <= maxa do
  { test idx <= maxb then
      c := byte idx of b
    else
      c := 0;
    byte idx of a := c;
    idx +:= 1 } }
 
let strcpy_n_to_f(a, wordsa, b) be                  // normal to fixed
{ let maxa = wordsa * 4 - 1, idx = 0, c;
  while idx <= maxa do
  { c := byte idx of b;
    if c = 0 then
      break;
    byte idx of a := c;
    idx +:= 1 }
  while idx <= maxa do
  { byte idx of a := 0;
    idx +:= 1 } }
 
let strcpy_f_to_n(a, wordsa, b, wordsb) be          // fixed to normal
{ let maxa = wordsa * 4 - 2, maxb = wordsb * 4 - 1, idx = 0, c;
  while idx <= maxa do
  { c := byte idx of b;
    if c = 0 then
      break;
    byte idx of a := c;
    idx +:= 1 }
  byte idx of a := 0 }
 
let write_fixed(iosb, s, words, f) be
{ let max = words * 4 - 1, i = 0, full = false;
  if numbargs() > 3 then
    full := f;
  while i <= max do
  { let c = byte i of s;
    test c = 0 then
      test full then
        writech(iosb, ' ')
      or
        break
    or
      writech(iosb, c);
    i +:= 1 } }
 
 
let exp(base, exponent) be {
   test exponent = 0 then
   resultis 1
   else {
     let result = 1;
     for i = 0 to exponent - 1 do {
       result *:= base; }
     resultis result;
    }
}
let size_calc() be {
  sizes ! 0 := exp(2, 9);
  sizes ! 1 := sizes ! 0/ 4 * 512;
  for i = 2 to 9 do {
  sizes ! i := 128 * sizes ! (i-1);}
}

let format_disc(name) be {
  let op, next, block;
  op := devctl(dc$discclear, 1);
  if op < 0 then
    returnto(command_loop, op);
 
  size_calc();
    
  total_blocks := devctl(dc$disccheck, 1);
  if total_blocks < 3 then {
    error_reason := "devctl(dc$disccheck failed in format";
    returnto(command_loop, err$software) }
  $memory_zero(superblock, 128);
  list_blocks := (total_blocks / 128) + 1;
 
  superblock ! list.first := 1;
  superblock ! list.last := list_blocks;
  superblock ! list.pointer := 0;
  superblock ! free.blocks := total_blocks - list_blocks - 2; //superblock and rootdir
  superblock ! rootdir.index := list_blocks + 1;
  superblock ! sb_firstfreeblock := list_blocks + 2;
  superblock ! sb_datetime := seconds();
 
 
//writing free block list
  block := superblock ! list.first;
  next := superblock ! rootdir.index + 1;
  write(tty, "starting free block number: %d\n", next);
  while block <= superblock ! list.last do {
     let b = vec(128);
     for i = 0 to 127 do {
        test next <= superblock ! free.blocks then
          b ! i := next
        else
          b ! i := 0;
        next +:= 1;
     }
    op := devctl(dc$discwrite, 1, block, b);
    if op < 0 then
      returnto(command_loop, op);
    write(tty, "last element in block number in block %d\n", b ! 127);
    write(tty, "next free block number: %d\n", next);
    block +:= 1;
  }
 
//setting default window (first two blocks of free block list)
  op := devctl(dc$discread, 1, leftwindow, window);
  if op < 0 then
    returnto(command_loop, op);
  op := devctl(dc$discread, 1, rightwindow, window+128);
  if op < 0 then
    returnto(command_loop, op);
 
  write(tty, "\n");
  write(tty, "total blocks on disc: %d\n", devctl(dc$disccheck, 1));
  write(tty, "first block used in free block list: %d\n", superblock ! list.first);
  write(tty, "last block used in free block list: %d\n", superblock ! list.last);
  write(tty, "\n");
 
  strcpy_n_to_f(superblock + sb_name, sb_name_lengthwords, name);
  op := devctl(dc$discwrite, 1, superblock_pos, superblock);
  if op < 0 then
    returnto(command_loop, op);
  $memory_zero(rootdir, 128);
  op := devctl(dc$discwrite, 1, superblock ! rootdir.index, rootdir);
  if op < 0 then
    returnto(command_loop, op);
  resultis total_blocks }
 
let mount_disc() be {
  let op, ignore;
  total_blocks := devctl(dc$disccheck, 1);
  if total_blocks < 3 then {
    error_reason := "devctl(dc$disccheck) failed in mount";
    returnto(command_loop, err$software); }
  op := devctl(dc$discread, 1, superblock_pos, superblock);
  if op < 0 then
    returnto(command_loop, op);
  op := devctl(dc$discread, 1, superblock ! rootdir.index, rootdir);
  if op < 0 then
    returnto(command_loop, op);
 
  ignore := (superblock ! list.pointer / 128);
  op := devctl(dc$discread, 1, ignore+1, window);
  leftwindow := ignore + 1;
  op := devctl(dc$discread, 1, ignore+2, window+128);
  rightwindow := ignore + 2;
  window.pointer := superblock ! list.pointer - (ignore * 128);
 
  disc_mounted := true;
  resultis total_blocks }
 
 
let dismount_disc() be {
  let op;
  unless disc_mounted do
    resultis 1;
  op := devctl(dc$discwrite, 1, superblock_pos, superblock);
  if op < 0 then
    returnto(command_loop, op);
  op := devctl(dc$discwrite, 1, superblock ! rootdir.index, rootdir);
  if op < 0 then
    returnto(command_loop, op);
  //save free block window to disk
  op := devctl(dc$discwrite, 1, free.blocks ! window);
  if op < 0 then
    returnto(command_loop, op);
  disc_mounted := false;
  //status();
  resultis 1; }
 
 
let show_superblock() be
{ unless disc_mounted do
    mount_disc();
  write(tty, "number of blocks: %d\n", total_blocks);
  write(tty, "disc name: \"%0*s\"\n", sb_name_lengthwords * 4, superblock + sb_name);
  write(tty, "formatted: %t\n", superblock ! sb_datetime);
  write(tty, "root directory is in block %d\n", superblock ! rootdir.index);
  write(tty, "first free block is block %d\n", superblock ! sb_firstfreeblock) }
 
 
let show_root_directory() be
{ let total = 0;
  unless disc_mounted do
    mount_disc();
  for offset = 0 to 127 by sizeof_de do
  { if rootdir ! offset = 0 then
      loop;
    total +:= 1;
    write(tty, "%*s with header block at %d,\n",
               de_name_lengthwords * 4, rootdir + offset + de_name, rootdir + offset + de_blocknum); }
  write(tty, "total %d files\n", total) }
 
 
let get_root_directory_entry(fname) be
{ let thisname = vec(de_name_lengthwords + 1);
  for offset = 0 to 127 by sizeof_de do
    if rootdir ! offset <> 0 then
    { strcpy_f_to_n(thisname, de_name_lengthwords + 1, rootdir + offset + de_name, de_name_lengthwords);
      if thisname %equals fname then
        resultis rootdir + offset; }
  error_reason := "file not found";
  resultis err$software }
 
 
let shift_rightwindow() be {
  let op;
  leftwindow := rightwindow;
  rightwindow := leftwindow + 128;
  op := devctl(dc$discread, 1, leftwindow, window);
  if op < 0 then
    returnto(command_loop, op);
  op := devctl(dc$discread, 1, rightwindow, window+128);
  if op < 0 then
    returnto(command_loop, op);
  window.pointer := window.pointer+128;
  write(tty, "shifted window right to blocks %d, %d\n", leftwindow, rightwindow);
}
 
let shift_leftwindow() be {
  let op;
  rightwindow := leftwindow;
  leftwindow := rightwindow - 128;
  op := devctl(dc$discwrite, 1, leftwindow, window);
  if op < 0 then
    returnto(command_loop, op);
  op := devctl(dc$discwrite, 1, rightwindow, window+128);
  if op < 0 then
    returnto(command_loop, op);
  window.pointer := window.pointer - 128;
  write(tty, "shifted window left to blocks %d, %d\n", leftwindow, rightwindow);
 
}
 
 
let free_block() be {
   let b;  
   if window.pointer >= 128 then {
     let r = shift_rightwindow();
     if r < 0 then {
       resultis r;
        }
    }
   
   b := window ! window.pointer;
   if b = 0 then {
     error_reason := "disc is full";
     resultis err$software;
    }

   window.pointer +:= 1;
   resultis b;
}
 
let make_block_free(b) be {
  if window.pointer <= 0 then {
    let r = shift_leftwindow();
    if r < 0 then {
      resultis r;
        }
    }

  window.pointer -:= 1;
  window ! window.pointer := b;
  resultis 1;
}
 
let find_level(fsize) be {
  for level = 0 to 9 do
    if sizes ! level >= fsize then
      resultis level;
}
 
 
let enter_into_root_directory(fname, blocknum) be
{ unless disc_mounted do
    mount_disc();
  for offset = 0 to 127 by sizeof_de do
    if rootdir ! offset = 0 then
    { let entry = rootdir + offset;
      strcpy_n_to_f(entry + de_name, de_name_lengthwords, fname);
      entry ! de_blocknum := blocknum;
      resultis offset }
  error_reason := "root directory full";
  resultis err$software }
 
 
let writechar_disc(iosb, c) be
{ if iosb ! iosb_pos >= iosb ! iosb_size then
{  error_reason := "file too big";
           resultis err$software }
 byte iosb ! iosb_pos of iosb ! iosb_buffer := c;
 iosb ! iosb_pos +:= 1;
 resultis 1; }


let readchar_disc(iosb) be
{ let c;
  if iosb ! iosb_pos >= iosb ! iosb_size then
    resultis EOF;
  c := byte iosb ! iosb_pos of iosb ! iosb_buffer;
  iosb ! iosb_pos +:= 1;
  resultis c; }
 
 
let unreadchar_disc(iosb) be
{ if iosb ! iosb_pos <= 0 then
  { error_reason := "unreadchar at beginning of file";
    resultis err$software }
  iosb ! iosb_pos -:= 1;
  resultis 1 }
 
 
let close_disc_r(iosb) be
{ freevec(iosb ! iosb_buffer);
  freevec(iosb);
  resultis 1 }
 
 
let close_disc_w(iosb) be
{
 let r;
 if iosb ! iosb_pos > 0 then
  { let r = devctl(dc$discwrite, 1, iosb ! iosb_close, iosb ! iosb_buffer);
    if r < 0 then
      resultis r;
    rootdir ! (iosb ! iosb_dirent + de_length) := iosb ! iosb_pos }
  freevec(iosb ! iosb_buffer);
  freevec(iosb);
  resultis 1 }
 
 
let disc_open_w(fname) be
{ let b, e, r;
  b := free_block();
  if b < 0 then
    resultis b;
  e := enter_into_root_directory(fname);
  if e < 0 then
    resultis e;
  r := newvec(sizeof_iosb);
  r ! iosb_ichar := illegal_readch;
  r ! iosb_bchar := illegal_unreadch;
  r ! iosb_ochar := writechar_disc;
  r ! iosb_close := close_disc_w;
  r ! iosb_unit := 1;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := 512;
  r ! iosb_dirent := e;
  resultis r
}

let write_file(fname, r) be
{
  let c;
  let buff = vec(200);
  while true do {
     c := readstr(tty, buff, 200);
     
     if buff !0= '*' bitand buff !1 = 0 then break;
    
     writechar_disc(r, c);
        }
}

 
let read_file(fname, iosb_size) be
{ let c;
  let n;
  if n = 0 then n := 0x7FFFFFFF;
  while n > 0 do {
        c := readchar_disc(iosb_size, c);
        if c = -1 then break;
        writech(c);
        n -:= 1
  }
  write('\n');
}
 
 
let disc_open_r(fname) be
{ let v, r, e;
  e := get_root_directory_entry(fname);
  if e < 0 then
    resultis e;
  r := newvec(sizeof_iosb);
  r ! iosb_ichar := readchar_disc;
  r ! iosb_bchar := unreadchar_disc;
  r ! iosb_ochar := illegal_writech;
  r ! iosb_close := close_disc_r;
  r ! iosb_unit := 1;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := e ! de_length;
  v := devctl(dc$discread, 1, e ! de_blocknum, r ! iosb_buffer);
  if v < 0 then
  { freevec(r ! iosb_buffer);
    freevec(r);
    error_reason := "failed to read file contents";
    resultis v }
  resultis r }
 
 
let open(fname, mode) be
{
  let open_disc(fname, read) be
  { unless disc_mounted do
      mount_disc();
    test read then
      resultis disc_open_r(fname)
    or
      resultis disc_open_w(fname) }
 
  let read;
 
  test mode = 'r' \/ mode = 'R' then
    read := true
  or test mode = 'w' \/ mode = 'W' then
    read := false
  or
  { error_reason := "invalid mode for open";
    resultis err$software }
 
  test fname %begins_with "d/" then
  { skip_chars_in(2, fname);
    resultis open_disc(fname, read) }
  or test fname %begins_with "t/" then
  { skip_chars_in(2, fname);
    test read then
      resultis tape_open_r(fname)
    or
      resultis tape_open_w(fname) }
  or test fname %equals "tty/" then
    resultis tty
  or
    resultis open_disc(fname, read) }
 
 
let delete_file(fname) be
{ let e;
  test fname %begins_with "t/" then
  { error_reason := "Can't delete tape files\n";
    returnto(command_loop, err$software) }
  or if fname %equals "tty/" then
  { error_reason := "Can't delete keyboard or monitor\n";
    returnto(command_loop, err$software) }
  if fname %begins_with "d/" then
    skip_chars_in(2, fname);
  e := get_root_directory_entry(fname);
  if e < 0 then
    resultis e;
  e ! de_name := 0;
  resultis 1 }
 
let create_file(fname) be {
  let op, blocknum, enter_entry, level, index_block, index_blocks;
  let hb = vec(128);
  blocknum := free_block();
  if blocknum < 0 then
    resultis blocknum;
 
  for i = 0 to 127 do
  hb ! i := 0;
 
  hb ! hb_startblock := blocknum + 1;
  hb ! hb_length_byte := 0;
  hb ! hb_buff := newvec(128);
  hb ! hb_buff_pos := 0;
 
  for i = 0 to 127 do
  (hb ! hb_buff) ! i := 0;
 
  hb ! hb_block := blocknum;
  hb ! hb_curr_wblk := hb ! hb_startblock;
  hb ! hb_createtime := seconds();
  hb ! hb_modtime := hb ! hb_createtime;
 
  level := find_level(hb ! hb_length_byte);
  hb ! hb_file_level := level;
  
 // index_blocks := vec(level + 1);
 // for i = 0 to level do {
 // index_block := free_block();
 //   if index_block < 0 then 
 //     error_reason := "failed to allocate index block";
 //     resultis err$software; 
 // index_blocks ! i := index_block;
 // }
 // hb ! hb_index_index_blocks := index_blocks;
 
  op := devctl(dc$discwrite, 1, blocknum, hb);
  if op < 0 then
    returnto(command_loop, op);
  enter_entry := enter_into_root_directory(fname, blocknum);
  if enter_entry < 0 then {
    error_reason := "failed to add file to root directory";
    returnto(command_loop, err$software); }
  resultis 1; }
 
 
let file_protections(fname, action) be {
  let op, hblock, protect_byte, bits, protection;
  let entry = get_root_directory_entry(fname);
  if entry < 0 then {
    returnto(command_loop, err$software); }
  hblock := rootdir ! (entry + de_blocknum);
  op := devctl(dc$discread, 1, hblock, headerblock);
  if op < 0 then
    returnto(command_loop, op);
  protect_byte := byte 0 of headerblock;
  bits := selector 3 : 5 from protect_byte;
  write(tty, "protections: %d (delete, modify, exe, 1 = allowed)\n", bits);
  if action <> 1 then {
    write(tty, "enter protection to switch permission (ex. delete, modify, etc.)\n");
    readstr(tty, protection, 10);
 
    if protection %equals "delete" then
    { test bits ! 0 = 1 then
        bits ! 0 := 0
      else
        bits ! 0 := 1; }
    if protection %equals "modify" then
    { test bits ! 1  = 1 then
        bits ! 0 := 0
      else
        bits ! 0 := 1; }
    if protection %equals "exe" then
    { test bits ! 2  = 1 then
        bits ! 0 := 0
      else
        bits ! 0 := 1; }
 
    byte 0 of headerblock ! hb_fileinfo := bits + 00000;
    op := devctl(dc$discwrite, 1, hblock, headerblock);
    resultis 1; }
 resultis 1; }
 
 
let create_file_from_file(tof, fromf) be
{ let line = vec(40), r, prompt = false;
  if fromf = tty then
  { abandon_input_line(tty);
    writestr(tty, "enter lines of text, lone * for end\n");
    prompt := true; }
  while true do
  { if prompt then
      writestr(tty, "< ");
    r := readline(fromf, line, 40);
    test prompt then
      if line %equals "*" then
        break
    or if r = EOF then
      break;
    write(tof, "%s\n", line) }
  resultis 1 }
 
 
let help() be
{ writestr(tty, "commands:\n");
  writestr(tty, "  exit\n");
  writestr(tty, "  help.             just prints this again\n");
  writestr(tty, "  format <name>    format the disc, give it that name\n");
  writestr(tty, "  info             display information mostly from superblock\n");
  writestr(tty, "  dir              list all directory entries\n");
  writestr(tty, "  create <a>       create file by name of a\n");
  writestr(tty, "  read <a>         open file <a> for read\n");
  writestr(tty, "  write <a>        open file <a> for write\n");
  writestr(tty, "  vprotect <a>     view protections of file a\n");
  writestr(tty, "  chprotect <a>    change protections of file a\n");
  writestr(tty, "  copy <a> <b>     create file b as a copy of file a\n");
  writestr(tty, "  del <a>          delete file, only for disc files\n");
  writestr(tty, "filenames:\n");
  writestr(tty, "  d/name           is a disc file\n");
  writestr(tty, "  t/name           is a tape file\n");
  writestr(tty, "  tty/             keyboard or monitor (note the / to prevent ambiguity)\n");
  writestr(tty, "  (other)          assumed to be a disc file\n") }
 
 
let start() be
{ init();
  command_loop := thiscall();
  help();
  while true do
  { let command = vec(20), fname = vec(20), fromfile = vec(20), input = vec(40), r, op;
    error_reason := nil;
    writestr(tty, "> ");
    readstr(tty, command, 20);
 
    test command %equals "exit" then
    { dismount_disc();
      break }
 
    or test command %equals "help" then
      help()
 
    or test command %equals "info" then
      show_superblock()
 
    or test command %equals "dir" then
      show_root_directory()
 
    or test command %equals "format" then
    { readstr(tty, fname, 20);
      r := format_disc(fname);
      test r >= 0 then
        write(tty, "%s formatted with %d blocks\n", fname, r)
      or
        write(tty, "error %d: %s\n", r, error_names ! -r) }
 
    or test command %equals "create" then
    { readstr(tty, fname, 20);
      op := create_file(fname);
      if op < 0 then
        write(tty, "error creating file\n", op); }
 
    or test command %equals "read" then
    {
      readstr(tty, fname, 20);
      r := open(fname, 'r');
      read_file(fname, iosb_size);
      close_disc_r(r ! iosb_size);
      if op < 0 then
      { perror(op, "opening (r)", fname);
        loop }
      writestr(tty, "successfully opened %s\n", fname); }
 
    or test command %equals "write" then
        {
      readstr(tty, fname, 20);
      r := open(fname, 'w');
      write(tty, "Begin writing into file, enter '*' when done\n");
      write_file(fname, r);
      close_disc_w();
      if op < 0 then
      { perror(op, "writing (w)", fname);
        loop }
      }
 
    or test command %equals "vprotect" then
    { readstr(tty, fname, 20);
      op := file_protections(fname, 1);
      if op < 0 then
        write(tty, "error viewing protections\n"); }
 
    or test command %equals "chprotect" then
    {  readstr(tty, fname, 20);
       op := file_protections(fname, 2);
       if op < 0 then
         write(tty, "error viewing and/or changing protections\n"); }
 
    or test command %equals "copy" then
    { let outf, inf, r;
      readstr(tty, fromfile, 20);
      readstr(tty, fname, 20);
      inf := open(fromfile, 'r');
      if inf < 0 then
      { perror(inf, "opening (r)", fromfile);
        loop }
      outf := open(fname, 'w');
      if outf < 0 then
      { perror(outf, "opening (w)", fname);
        loop }
 
      r := create_file_from_file(outf, inf);
 
      if r < 0 then
        perror(inf, fromfile, fname);
      r := close(outf);
      if r < 0 then
        perror(inf, "closing (r)", fromfile);
      r := close(inf);
      if r < 0 then
        perror(inf, "closing (w)", fname) }
 
    or test command %equals "del" then
    { readstr(tty, fname, 20);
      r := delete_file(fname);
      if r < 0 then
        perror("delete", fname) }
 
    or
    { abandon_input_line(tty);
      write(tty, "%s???\n", command); } } }
