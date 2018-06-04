#include <stdlib.h>
#include "suif.h"
#include <picoextn/annote.h>
#include <useful.h>
#include <vector>
#include <string>
#include <iterator>
#include <picoextn.h>

#include "compute_annote.cc"
using namespace std;
//#include <picoextn.h>

/* This pass creates instrumented code  from dismantled code 

USAGE
            ./simu_instrument input.spd output.spd
    
            Convert_Aggregate pass must be run prior to this pass

DESCRIPTION
    Convert_Aggregate pass dismantles structure access to  scalars and arrays
    The dismantled version can no longer link with original driver because the  dismantled variable names are different from those used in driver
    simu_instrument takes the dismantled code and  constructs code linkable with driver by replacing access of dismantled variables by original variables


EXAMPLE

input.c

    struct s
    {
        int x,y;
    } A

A.y = 1
    
after convert_aggregate
    
    A_y =1 
    
after simu_instrument 
        
    *( (char*) A + 4 ) = 1


        
*/


/*
    Description of the algorithm 

    main: compute_annotations , do_proc

            compute_annotations  traverses the global symbol table and for each dismantled variable, gets the original symbol using the annote k_container_aggregate_symbol. then  compute_info on the original symbol is called which calculates descriptor information ( such as address of original symbol, offset , array sizes etc )

            do_proc : finds whether an instruction's address is a dismantled variable. If so replace itby address of original symbol (using descriptor information )

*/

//int debug=1;
/* prototype declarations */


type_node* type_int_8;
type_node* type_ptr_int_8;

bool is_aggregate(type_node*);


char* k_struct_info;
char* k_debug;


#define dbprintf printf 


instruction* process_insn(instruction* insn,  vector<int> &array_sizes);

bool get_annote(var_sym * sym, var_sym* &original_sym, int& offset , vector<int>& array_sizes) {
    bool annote_found = false;
    if( sym->peek_annote(k_field_access_signature)  )
    {
        annote_found = true;
        immed_list* iml=(immed_list*) sym->peek_annote(k_field_access_signature);
        immed_list_iter iter(iml);    
        immed im = iter.step();
        original_sym = (var_sym*)im.symbol();
        im = iter.step();
         offset = im.integer();

        int i=0;
        while( ! iter.is_empty() )
        {
            int size = (iter.step()).integer();     
            array_sizes.push_back( size ) ;
        }
    }
    return annote_found;

}

////////////////////////////////////////////////////////////////////////////////////////////


void mark_ins(instruction *ins, char* str)
{    
        if( ins->peek_annote(k_debug) ) return;    
      immed_list* iml=new immed_list;    iml->append(immed(str));
        ins->set_annote(k_debug,iml );    
}

bool is_marked(instruction *ins)
{
    if( ins->peek_annote(k_debug) ) return true;
    return false;
}



instruction* emit_ins_plus_offset(instruction* ins, int offset)
{
    if(offset==0) return ins;
    in_ldc * ldc= new in_ldc() ; ldc->set_value(offset) ; ldc->set_result_type(type_signed);
    in_rrr  * result= new in_rrr( io_add , ins->result_type() , operand() , operand(ins), operand(ldc));
    return result;

}

int  get_array_indices(var_sym* sym  , vector<int> & array_indices)
{
    //k_index_in_source_array is a flat annotation - the first element is the name of the element scalarized,
    // the subsequent elements are the index numbers for eg. if a[2][3] got scalarized to a_2_3 the annotation list
    // would be { a,2,3 }
    // pre-condition  : the annote's structure should not be change. 
    if( !sym->peek_annote(k_index_in_source_array) )  return -1;
    immed_list *iml = lookup_annote(sym, k_index_in_source_array, iml);
    immed_list_iter it(iml);
	 it.step(); // skip the name
    int count =0;
    while( !it.is_empty() ) 
    {
        count++;
        int index = it.step().integer() ;
        array_indices.push_back(index);
    }
    return count;

}

instruction* get_sym_ldc(var_sym* sym,  vector<int> & array_sizes )
{
    int offset;
    var_sym * orig_sym;
    if(! get_annote(sym, orig_sym, offset, array_sizes) )      return NULL;
        
	 var_sym *vs = orig_sym;
     in_ldc* ldc=new in_ldc;

     bool orig_var_is_ptr =  vs->type()->unqual()->is_ptr();
     bool new_var_is_ptr  =  sym->type()->unqual()->is_ptr();
     if(   sym->type()->unqual()->is_ptr() ) {
           ptr_type* ptr = (ptr_type*)sym->type()->unqual();

          if( !vs->type()->unqual()->is_ptr() )  
          {
               sym_addr* addr = new sym_addr(vs,0);
               ldc->set_value(*addr);
               ldc->set_result_type( sym->type()->unqual()) ;
               instruction* ins2= emit_ins_plus_offset(ldc, offset/8);
               mark_ins(ins2,"symtypeptr1");
               return ins2;
          }
          else 
          {
                in_rrr * cpy = new in_rrr(io_cpy,ptr, operand(), operand(vs),operand());
                instruction* ins2= emit_ins_plus_offset(cpy, offset/8);
                mark_ins(ins2,"symtypeptr2");
                return ins2;
          }
    }
    if( sym->type()->unqual()->is_array() ) 
    {
         sym_addr* addr = new sym_addr(vs,offset) ;
         array_type* arr= (array_type*) sym->type()->unqual();
         ldc->set_value( *addr );
         ldc->set_result_type( type_s8->ptr_to() );
         mark_ins(ldc,"symtypeptr3");
         return ldc;
    }
    else 
    {
            sym_addr* addr = new sym_addr(vs,offset) ;
            ldc->set_value( *addr );
            ldc->set_result_type( sym->type()->ptr_to());
            mark_ins(ldc,"symtypeptr4");
            return ldc;
    }
    assert(0);
    return NULL;
}

/*type_node* get_next_level_ptr(type_node* type)
{
	ptr_type* p= (ptr_type*)type; // ptr to array of int
	return  ( ((array_type*)(p->ref_type()))->elem_type())->ptr_to();
}*/


var_sym* get_symbol_from_ldc(in_ldc* ldc)
{
    immed im = ldc->value();
	var_sym* sym=NULL;
    if( im.is_symbol())  
	{
       sym = (var_sym*) im.symbol();
	}
	return sym;
	
}

var_sym* get_symbol_from_cvt(in_rrr* ins)
{
	operand op(ins->src1_op());
	if( op.is_symbol())
	{
		return (var_sym*)op.symbol();
	}		
	assert(0);
	return NULL;

}

// stores info about dismantled variable - namely the original var_sym , the offsets , the array sizes and types
class sym_info
{
		var_sym* dismantled;
		queue<int> sizes;
		queue<int> offsets;
		queue<type_node*> types;
		queue<operand> array_indices;
		in_array*  arr;
		bool is_ptr;
		type_node* cvt_type;
	public:

		var_sym* original;
	
			sym_info() { arr=NULL; dismantled=NULL;  original=NULL; is_ptr=false; cvt_type=NULL;
				 }
	
			void set_array(in_array * a) 
			{
				arr=a;
			}	
			void set_symbol(var_sym* sym) 
			{
				dismantled = sym;
				original = NULL;
				var_sym* parent = get_parent_var(sym);
				if( parent)
					original= compute_info1(parent, sizes , offsets, types);
				else 
					fprintf(stderr, "\nwarning: no parent sym for %s", sym->name());
				
			}
			void set_cvt_type(type_node* t) { cvt_type=t->unqual(); }

			var_sym* get_original() { return original; }
		

			instruction* get_base() 
			{
				 assert(dismantled);

				if(dismantled->peek_annote(k_no_instrument)) return NULL;
				 return get_array();
			}
			void set_ptr() { is_ptr=true; }	
			instruction* get_ptr() 
			{
				assert(dismantled);
				if(dismantled->peek_annote(k_no_instrument)) return NULL;
				fprintf(stderr,"get_ptr()");
				type_node* t= dismantled->type()->unqual();	
				instruction* ins=NULL;
				type_node* type=NULL;
				int offset=0;
				while(! offsets.empty() )  {
					//assert(0);
					 offset+= next_offset();
					type=next_type();
				//	if(ins) 
				//		 ins = new in_rrr(io_add,  (next_type()) , operand() , operand(ins) , const_int_op( offset/8 ));
				//	else 
				//		ins = new in_rrr(io_add,  (next_type()) ,operand() , operand(original), const_int_op( offset/8));
					
				
				}
				ins = new in_rrr(io_add,  type , operand() , operand(original) , const_int_op( offset/8 ));

				if(ins)
				ins->append_annote(k_fields );
				mark_ins(ins,"get_ptr");
				return ins;

			}
					// handles scalarization of array base instructions
			instruction * get_array()  {
			   int count=0; 
				queue<int> temp;
			   count = get_scalarized_var_info(dismantled,temp)  ;
				while( !temp.empty()) { array_indices.push(  const_int_op(temp.front())) ; temp.pop(); }
			
				if(arr) {
					count += arr->dims();
		            for(int ind= 0 ; ind < arr->dims() ; ind++)  
    		        {
        	        	operand op( arr->index(ind) );
						array_indices.push(op);
    	        	}

				}

				 else if (is_ptr)  {
					count +=  1;
	
			         for(int ind= 0 ; ind < 1 ; ind++)  
    		        {
        	        	operand op( const_int_op(0) );
						array_indices.push(op);
						//types.push( dismantled->type()->unqual() );
    	        	}

				}
				
				if(original && original->type()->unqual()->is_ptr())  {
							return get_ptr(); 
				}
				else return get_array0(count);
			 }
			//helper function
			instruction* get_array0(int count) {
				//base case
				if( count == 0 ) {
							 return get_ldc();
				}
				instruction * base = get_array0( count-1 );
				if( !base ) return NULL;
				in_array* newarr;
				type_node* type= next_type(); 
				if(!type)  { 
					fprintf(stderr,"warning: %s is not handled due to type mismatch. count=%d", dismantled->name() ,count);
					return NULL;
				}
				newarr= new in_array(  type , operand(),operand(base),  next_size()  ,1,  next_offset());
				newarr->set_index(0, next_index() ) ;
				return newarr; 
				
			}
			void set_array_base(in_ldc* ins)  {  
					var_sym* sym = get_symbol_from_ldc(ins);
					assert(sym);
					if(sym->peek_annote(k_no_instrument))  return ;
					set_symbol(sym);
			}
		
			in_ldc* get_ldc() {
					if(original) {
						fprintf(stderr, "\n%s==>%s" , dismantled->name(),original->name() );
						in_ldc* ldc =new in_ldc();
						if( cvt_type)  ldc->set_result_type( cvt_type) ;
		   		        else ldc->set_result_type( next_type()  );
						ldc->set_value(immed(original, next_offset() ));
						return ldc;
					}
					return NULL;
			}

			int next_size() {
				if(sizes.empty()) return 0;
				int t= sizes.front() ; sizes.pop();	return t;
			}
			
			int next_offset() {
				if( offsets.empty() ) return 0;
				int t= offsets.front(); offsets.pop(); return t;
			}
			type_node* next_type() { 
				if (types.empty()) return NULL;
				type_node* t=types.front(); types.pop(); return t;
			}
			operand next_index() {
				operand t= array_indices.front() ; array_indices.pop(); return t;
			}

};



instruction*  process_insn(instruction* ins);
// process top level instruction
void process_insn_top(instruction* insn)
{

    // Process everything (like src_ops, args, ldc values ) other than dst_op's 

    instruction * ins_mod ;
    ins_mod= process_insn(insn);
    if(ins_mod==NULL ) ins_mod=insn;

    /** 
		now process dst_op - top level instructions  can have only symbols as  dst_op
        other instruction's have only instructions as dst_op 
	**/
    operand op(insn->dst_op());
	
    if(op.is_symbol())  
    {
        var_sym* sym=op.symbol();
		sym_info info;	info.set_symbol(sym);
		//fprintf(stderr, "\n$ %s" ,sym->name());
		if(info.original) {
		//	fprintf(stderr, "# %s", sym->name());
			instruction* ins = info.get_base();		
			if(ins)   {
	            in_rrr * str =new in_rrr( io_str , ins_mod->result_type() ,  operand(), operand(ins) , operand(ins_mod->clone() )  );
				replace_instruction(insn, str);
			}

		}
    }
	if (op.is_instr()) assert(0);
}


//change it to get_new_instr
instruction*  process_insn(instruction* ins)
{
   assert(ins); 
	if( ins->peek_annote(k_no_instrument) ) return ins;
	// move this to class syminfo
	if( ins->format() == inf_ldc )
	{
		var_sym* sym = get_symbol_from_ldc( (in_ldc*)ins);
		sym_info info;
		if(!sym) return ins;
		info.set_symbol(sym);
		if ( sym->type()->unqual()->is_ptr() || sym->type()->unqual()->is_array())  info.set_ptr(); 
		instruction*  newins = info.get_base();
		if(!newins) return ins;
		replace_instruction(ins,newins);
		return newins;
		//((in_ldc*)ins)->set_value( ldc->value());
	}

	
    if( ins->format() == inf_array )
    {
        in_array* arr = (in_array*)ins;
		
        operand op( arr->base_op());
        if( op.is_instr() ) 
        {
            instruction* base_instr = op.instr();
            int arr_dim = arr->dims();
			instruction* newarr=NULL;
			sym_info info ;
			info.set_array(arr);

			if(base_instr->format() == inf_ldc) {
					var_sym* sym = get_symbol_from_ldc( (in_ldc*)base_instr);
					if(!sym) return ins;
					if(sym->peek_annote(k_no_instrument))  return ins;
					info.set_symbol(sym);
					if ( sym->type()->unqual()->is_ptr() || sym->type()->unqual()->is_array())  info.set_ptr(); 
					newarr= info.get_base();
			}
			else if (base_instr->opcode()==io_cvt) {
					var_sym* sym= get_symbol_from_cvt( (in_rrr*)base_instr);
					if(!sym) return ins;
					if(sym->peek_annote(k_no_instrument))  return ins;
					info.set_symbol(sym);
					info.set_cvt_type( base_instr->result_type());
					if ( sym->type()->unqual()->is_ptr() || sym->type()->unqual()->is_array())  info.set_ptr(); 
					newarr= info.get_base();
				/*
				var_sym* sym = ((in_rrr*)base_instr)->src1_op().symbol();
				info.set_symbol(sym,arr);
				 newarr= info.get_base();*/
				//newarr= process_insn(base_instr);
				/*
				instruction* temp= process_insn(base_instr);
				if(!temp) return ins;
				info.set_array_base(temp );
				newarr= info.get_base();
				*/
			}
			else assert(0);
		
			if (newarr == NULL ) return ins;
			replace_instruction(arr,newarr);
            return newarr;
        }
        assert(0);
   }

    if( ins->format() == inf_cal ) {

         in_cal* cal= (in_cal*)ins;
         proc_sym* sym = proc_for_call(cal);

        /* do not instrument for calls like NPA_IN_OFFSET produced by simu_setup */    

        if( sym->peek_annote(k_no_instrument)  )  {  return cal;     }
         
        for(unsigned i=0;i < cal->num_args() ; i ++ )
        {
             operand op( cal->argument(i));
             if ( op.is_symbol() )  
             {
					sym_info info;
					info.set_symbol( op.symbol() );
					// TODO

					if( op.symbol()->type()->unqual()->is_ptr()  && info.original ) {
							
						//in_rrr * cpy =new in_rrr( io_cpy , op.symbol()->type() ,     operand(), operand( info.get_base() )  );

                        // cal->set_argument(i, operand(cpy));
						
						instruction* newins= info.get_base();
                        cal->set_argument(i, operand( newins ));
						mark_ins(newins, "call arg instru");


					}
					else 
					{
						if(info.original) {
					    	in_rrr * load =new in_rrr( io_lod , op.symbol()->type() ,     operand(), operand( info.get_base() )  );
	                        cal->set_argument(i, operand(load));
						}

					}
				
             }


             if( op.is_instr() )  {
                    instruction* new_instr=process_insn( op.instr() );
                    if( new_instr)   {
                            operand o; o.set_instr(new_instr);
                            cal->argument(i).remove();
                            cal->set_argument(i,o);
                            mark_ins(cal,"cal argument(ins)");
                     } 
              }
         }//for

     return cal;
   }


    for(unsigned i=0; i<ins->num_srcs(); i++) 
    {
        operand op(ins->src_op(i));
        if(op.is_instr())
        {        
            instruction* new_ins = process_insn(op.instr());
            if(new_ins) 
            {
                        ins->src_op(i).remove();
                        ins->set_src_op(i, new_ins);
                        mark_ins(ins, "source op is insn");
            }
                
        }
        else  if( op.is_symbol()) 
        {
				sym_info info ; 
				info.set_symbol(op.symbol());
				if( info.original )  {
					in_rrr * load =new in_rrr( io_lod , op.symbol()->type() ,     operand(), operand( info.get_base() )  );
    	            ins->set_src_op(i, operand(load));
        	         mark_ins(ins, "source op is symbol(var)");
				}

				
	

				/*
              instruction* address =  get_sym_ldc( op.symbol() ,  array_sizes) ;
              if(! address) continue;
              if( op.symbol()->type()->unqual()->is_ptr() ) 
              { 
                   in_rrr * cpy =
                        new in_rrr( io_cpy , op.symbol()->type()->ptr_to() ,     operand(), operand(address)  );
                   ins->set_src_op(i, operand(cpy));
                   mark_ins(ins, "source op is symbol(ptr)" );
              } 
              else
              {
                   in_rrr * load =new in_rrr( io_lod , op.symbol()->type() ,     operand(), operand(address)  );
                   ins->set_src_op(i, operand(load));
                   mark_ins(ins, "source op is symbol(var)");
              } */
         }
    } //for
    return ins;
}

void process(tree_node_list* tnl)
{
    tree_node_list_iter iter(tnl);
    while(!iter.is_empty())
    {
        tree_node* tn =iter.step();
        switch(tn->kind())
        {
            case TREE_FOR: 
                {
                    tree_for * tnf=(tree_for*)tn;
                    process(tnf->lb_list());
                    process(tnf->ub_list());
                    process(tnf->step_list());
                    process(tnf->landing_pad());
                    process(tnf->body());
                }
                break;
            case TREE_IF:
                {
                    tree_if* tni=(tree_if*)tn;
                    process(tni->header());
                    process(tni->then_part());
                    process(tni->else_part());
                }
                break;

            case TREE_LOOP:
                {
                    tree_loop* tnl=(tree_loop*) tn;
                    process(tnl->test());
                    process(tnl->body());
                }
                break;
            case TREE_BLOCK:
                {
                    tree_block* tnb= (tree_block*)tn;
					compute_field_access_signature(tnb->symtab());
                    process(tnb->body());
                }
                break;

            case TREE_INSTR:
                {
                    tree_instr *tnin=(tree_instr*) tn;
                    process_insn_top(tnin->instr());
                }
                break;
        }
    }
}

int get_offset_of_param(var_sym* sym )
{
        vector<int> array_sizes ; //unused
        char* name; //unused
        int offset=0;
        if( sym->peek_annote(k_container_aggregate_symbol) &&  !sym->peek_annote(k_no_instrument) )
        {
            if( sym->peek_annote(k_field_access_signature) ) {
                 immed_list* iml=(immed_list*) sym->peek_annote(k_field_access_signature);
                immed_list_iter iter(iml);    
                immed im = iter.step();
                im = iter.step();
                offset = im.integer();
            }
        }
        return offset; 
}


void handle_params(tree_proc* tp)
{

return;
set<string> uniq_param_names;
    
  sym_node_list_iter param_iter (tp->proc_syms()->params());

    while ( ! param_iter.is_empty() )  {
        sym_node* symnode= param_iter.step();
        var_sym* sym = (var_sym*)symnode;
		sym_info info; info.set_symbol(sym);
        var_sym* original_sym = info.original; 
        
        if(    original_sym   
            && uniq_param_names.insert(original_sym->name() ).second  // name is not already present
            /*&& sym->type()->is_ptr()*/ && sym->peek_annote(k_dismantled_param)   )  {
           
           // LDC <offset>    
           int offset= get_offset_of_param(sym);
           in_ldc* off= new in_ldc; off->set_value(immed(offset/8)); off->set_result_type(type_signed);
           in_rrr * subtract;
           subtract=new in_rrr(io_sub, sym->type(), operand(original_sym), operand(sym) , operand (off) );
           tp->body()->push(new tree_instr (subtract));
           subtract->prepend_annote(k_no_instrument, new immed_list);
        }
    }
                

}


void do_proc(tree_proc * tp)
{
    proc_sym * psym = tp->proc();
    curr_proc_symtab = tp->proc_syms();
    compute_field_access_signature(tp->proc_syms() ) ; 
    handle_params(tp);
    process(tp->body()); 
}


using namespace std;

#include <vector>
#include <string>
#include <map>



int main(int argc, char * argv[])
{
    start_suif(argc, argv);

    ANNOTE(k_field_access_signature,"field access signature", TRUE); 
    ANNOTE(k_debug, "debuginfo", TRUE);
    fileset->add_file(argv[1], argv[2] );
    global_symtab= fileset->globals();
    compute_field_access_signature(fileset->globals());
     fileset->reset_iter(); 
    file_set_entry *fse = fileset->next_file(); 

  fse->reset_proc_iter(); 
  proc_sym *ps; 
  while ((ps = fse->next_proc()) != 0) {
    if (!ps->is_in_memory())
      ps->read_proc(); 
    do_proc(ps->block()); 
    ps->write_proc(fse); 
    ps->flush_proc(); 
  }
  exit_suif(); 
    return 0;
}






