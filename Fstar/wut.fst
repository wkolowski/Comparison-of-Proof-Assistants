module Wut

type t =
{
    a : bool;
    b : (if a then bool else unit);
    c :
      (match a with
       | true -> begin
            match b with
              | true -> string
              | false -> unit
	    end
       | false    -> unit)
}
