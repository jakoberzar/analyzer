// NOMARSHAL PARAM: --set ana.activated "['base','threadid','threadflag','escape','fmode', 'OSEK', 'OSEK2', 'stack_trace_set','mallocWrapper']" --set ana.osek.oil 07-flags.oil --set ana.osek.flags[+] flag

int flag = 0;
int var = 0;

ISR(high)
{
  GetResource(r);
  ReleaseResource(r);
}

ISR(four)
{
  var = 0;
}

ISR(three)
{
  if (flag == 0) {
    var ++;
  }
}

ISR(two)
{
  flag = 1;
  int temp = var;       // RACE
  var = temp - var;     // RACE
//   assert(var = 0);      //
  flag = 0;
}

TASK(init)
{
  GetResource(r);
  var = 0;
  flag = 0;
  ReleaseResource(r);
}
