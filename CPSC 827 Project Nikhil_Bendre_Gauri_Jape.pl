# CPSC 827 Project Compiler
# Nikhil Bendre
# Gauri Jape
# 4th December 2010


my $sempopCnt;
my $sempopFlag=0;
my $j1;
my $semFoundNo;
my $semFoundType;
my $semFoundCol;
my $semExtractedRow;
my @semExtracted;
my $semLocalEntryFound=0;
my $semGlobalEntryFound=0;
my $semINTFlag=0;
my $semREALFlag=0;
my @storeIfLable;
my @storeForLabel;
my $countForLabels;
my $countIfLabels;
my $pointLabels;
my $endIpPARAM=0;
my $endOpPARAM=0;
my $semLocalError=0;
my $semGlobalError=0;
my $chckSub1=0;
my $chckSub2=0;

my $chckConversion1=0;
my $chckConversion2=0;
my $p1;

my $l1;
my $l2;

my $k1;
my $u1;
my $u2;
my $v1;
my $p2;
my $globalop2=0;

#Register Allocation
#Pragmatics Phase

my @register;
my @registerMain;
my $registerNo1;
my $registerNo2;
my $register1;
my $register2;
my $opFound;
my $regCnt;
my $totalReg=4;
my $totalSpill=$totalReg+2;
my $spillNum;
my $virtualReg1;
my $virtualReg2;
my $reg1Type;
my $reg2Type;
my $regResultNo;

my $regResult;

#Procedure related statements for Pragmatics
	my $procedure;
	my $procedureString;
	my @param_list;
	my $parameters;
	my $programName;
	my $procedureName;
	my $check_ref_value;
	my $check_if_no_parameter;
	my $matrixWord=0;
	
$registerMain[0]="eax";
$registerMain[1]="ebx";
$registerMain[2]="ecx";
$registerMain[3]="edx";
$registerMain[4]="VR1";
$registerMain[5]="VR2";


my %token_iden=(
	'start' => 1,
	'prog' => 2,
	'body' => 3,
	'declpart' => 4,
	'decllist' => 5,
	'decllist-' => 6,
	'declstat' => 7,
	'type' => 8,
    'procpart' => 9,
    'proclist' => 10,
    'proc' => 11,
    'prochead' => 12,
    'procname' => 13,
    'null-list' => 14,
    'fparmlist' => 15,
    'fparmlist-' => 16,
    'calltype' =>17,
    'execpart' => 18,
    'exechead' => 19,
    'startlist' => 20,
    'startlist-' => 21,
    'stat' => 22,
    'inputstat' =>23,
    'outputstat' => 24,
    'callstat' => 25,
    'callname' => 26,
    'aparmlist' => 27,
    'aparmlist-' => 28,
    'ifstat' => 29,
    'ifthen' => 30,
    'ifhead' => 31,
    'forstat' => 32,
    'forcond' => 33,
    'forhead' => 34,
    'assignstat' => 35,
    'astat' => 36,
    'bexpr' =>37,
    'bexpr-' => 38,
    'andexpr' => 39,
    'andexpr-' => 40,
    'notexpr' => 41,
    'notexpr-' => 42,
    'relexpr' => 43,
    'relexpr-' => 44,
    'aexpr' => 45,
    'aexpr-' => 46,
    'term' => 47,
    'term-' => 48,
    'primary' => 49,
    'primary-' => 50,
    'constant' => 51,
    'sexpr' => 52,
    'sexpr-' => 53,
    'integer' => 60,
    'real' => 108,
    'string' => 110,
    'var' => 56,
);

#for semantics 
my %rev_token = reverse %token_iden;
my @semanticStack;
push(@semanticStack,'%');
my @localSymbolTable;
my @handle;
my @tuple;
my @globalSymbolTable;
my @tupleRow;
my @lexString;
my $semanticStack_top=0;
my $semanticStack_cnt=0;
my $sem_input2;
# to save for semantics
my $sem_iden;
my $sem_checkresv;
my $sem_ascii;
my $sem_multiascii;
my $sem_int;
my $sem_real;
my $sem_string;
my $sem_input;
my @sem_list; 
my $globalSymbol_cnt=0;
my $globalSymbol_top=0;
my $checkProcFlag=0;
my $localSymbol_cnt=0;
my $localSymbol_top=0;
my $procName;
my $progNameSetFlag=0;
my $line2Cnt=0;
my $line2TotalLine;
my $singleCmtflag=0;
my $stringFound=0;
my @local_sem_list;
my @inputText;
my @lexarray;
my $lex_cnt=0;
my $cnt=0;
my $currInput;
my $noofLine;
my $tmpCnt;
my $popCnt;	
my $handleNotFound=0;
my $flag1;
my $popdContentsAraay1;
my $cmtflag=0;
my $popdContentsAraay;
my $CLEMhandle;
my $tmpValue;
my @localTuple;
my @sem_input1;
my $sem12proc=0;
my $checkSemanticError=0;
my $progName;

#for semantics 2
my $m=0;
my @sem_list2;
my $i1=0;
my @iden_list;
my @real_list;
my @int_list;
my $typeFinder;
my $typeSem;


#Declarations fore reading matrix 
my $line1;
my @tmparray;
my @matrix;
my $rit;
my $rit1=1;
my $cou=1;
my @tmpHandle;
my $tmpHandle1;
my $printRed=$lex_cnt;
my @printStack;
my @printArray;
my @outputArray;

#for procedure variables
my $procFlag=0; 
my @localSymbolTable1;
my $sem9=0;
my @BeforeSemanticStack;

readarr();

#Declaration for the reading the PRODUCTION MATRIX
my $line2;
my @tmparray1;
my @matrix1;
#readProd();
my @lenMat;
#my $j1=0;
my @popdContents;
#declaration for parser variable
my @stack;

my $stack_top=0;
my $stack_cnt=0;
my $handlewdoutright;
push(@stack,'%');
my $last_element;
my @new1;
my @lst;
my $temp123;
my @new2;
my @procHeadList;
my $procHead;

#Semantic Errors
my @checkSemErrors;
my @toVerifySemErrors;
my $checkSem1;
my $checkSem2;


#open(CON,'<',"newTestDataSem2.txt");
#open(CON,'<',"semErr.txt");
open(CON,'<',"sample_static.txt");

@inputText=<CON>;


open(OUT,'>>new12345.txt');
open(OP,'>>staticdemo1.txt');
open(SEM,'>>staticdemo1.txt');
open(CODE,'>>c:\hla\staticdemo2.hla');

my $totalLexCnt;
my $currentLexCnt;
my $earlierLexCnt;
my $count=0;
$noofLine=@inputText;
my $i=0;

my @mainFlag;
displayInfo();
displayInfo1();
displayInfo2();
initialFlag();
$mainFlag[2]=1;

my $keepLexCnt=$lex_cnt;
my $prodLine;
my $prodLine1;
my $prodCheck;
my $difference;
# for parser error recovery
my @tmpStack;
my $tmpStackCnt;

main($count);

#- Intial Flag Setting.
sub initialFlag
{
	 for (my $i = 0; $i < 32; $i++)
    {
        if($i == 1){
             $mainFlag[$i] = 1;
        }
        else{
            $mainFlag[$i] = 0;
        }
    }
}

sub searchGlobalSymbolTable
{
	my ($searchThru) = $_[0];
	@semExtracted=();
	$semFoundNo=0;
	my @semGlobalSymTable;
	my @semGlobalSymTable1;
	my @semSearchData;
	my $searchCnt=0;
	my $semS1;
	my $semS2;
	$semINTFlag=0;
	$semREALFlag=0;
	
	push(@semGlobalSymTable,@globalSymbolTable);
	while(@semGlobalSymTable!=())
	{
		@semGlobalSymTable1 = split(':',$semGlobalSymTable[0]);
		push(@semSearchData,$semGlobalSymTable1[0]);
		$searchCnt++;
		shift(@semGlobalSymTable);
	}
	
	if($searchCnt > 1)
	{
		#insert the data to be find out
		push(@semSearchData,$searchThru);
		$searchCnt++;
		
		$semS1 = $searchCnt-1;
		$semS2 = $semS1-1;
		
		while($semS2>=0)
		{
			if($semSearchData[$semS1] eq $semSearchData[$semS2])
			{
				$semFoundNo = $semS2;
				
				# now find that line from global symbol table
				# and take out the type
				
				#$semFoundNo indicates the row no in the global symbol table 
				#location 1 & 4 will give me the type & col value if needed
				@semExtracted = split(':',$globalSymbolTable[$semFoundNo]);
				$semGlobalEntryFound=1;
	
			}
			$semS2--;
			
		}
		
		
	}
	
	if(@semExtracted!=())
	{
		if($semExtracted[1]=~m/(REAL)/)
		{
		$semREALFlag =1;
		$NOTINTFLAG=1;
		}
		else
		{
			$semINTFlag=1;
			if($chckSub1==0)
			{
				$chckSub1=1;
			}
			else
			{
				$chckSub2=1;
			}
			
			if($chckConversion1==0)
			{
				$chckConversion1=1;
			}
			else
			{
				$chckConversion2=1;
			}	
		}
	}
	else
	{
		$semGlobalEntryFound=0;
		$semGlobalError=1;
	}
	
}

sub searchLocalSymbolTable
{
	my ($searchThru) = $_[0];
	@semExtracted=();
	$semFoundNo=0;
	
	my @semLocalSymTable;
	my @semLocalSymTable1;
	my @semSearchData;
	my $searchCnt=0;
	my $semS1;
	my $semS2;
	
	push(@semLocalSymTable,@localSymbolTable1);
	$semINTFlag=0;
	$semREALFlag=0;
	while(@semLocalSymTable!=())
	{
		@semLocalSymTable1 = split(':',$semLocalSymTable[0]);
		push(@semSearchData,$semLocalSymTable1[0]);
		$searchCnt++;
		shift(@semLocalSymTable);
	}
	
	if($searchCnt > 1)
	{
		#insert the data to be find out
		push(@semSearchData,$searchThru);
		$searchCnt++;
		
		$semS1 = $searchCnt-1;
		$semS2 = $semS1-1;
		
		while($semS2>=0)
		{
			if($semSearchData[$semS1] eq $semSearchData[$semS2])
			{
				$semFoundNo = $semS2;
				# now find that line from global symbol table
				# and take out the type
				# $semFoundNo indicates the row no in the global symbol table 
				# location 1 & 4 will give me the type & col value if needed
				@semExtracted = split(':',$localSymbolTable1[$semFoundNo]);
				$semLocalEntryFound=1;
			}
			$semS2--;
			
		}
		
	}
		
	if(@semExtracted!=())
	{
		
		if($semExtracted[1]=~m/(REAL)/)
		{
			$semREALFlag =1;
			$NOTINTFLAG=1;
		}
		else
		{
			$semINTFlag=1;
			if($chckSub1==0)
			{
				$chckSub1=1;
			}
			else
			{
				$chckSub2=1;
			}
			
			if($chckConversion1==0)
			{
				$chckConversion1=1;
			}
			else
			{
				$chckConversion2=1;
			}
		}
	}
	else
	{
		$semLocalEntryFound=0;
		$semLocalError=1;
		
		if($searchThru=~m/[0-9]/)
		{
			if($chckSub1==0)
			{
				$chckSub1=1;
			}
			else
			{
				$chckSub2=1;
			}
		}
		
	}
}

sub displayInfo
{
	#open (OUT, ">$outFile") or die "Error: Cannot open file: $!\n";
    print OUT "******************************************************************\n";
    print OUT "*********************** NIKHIL BENDRE & GAURI JAPE ****************\n";
    print OUT "******************************************************************\n";
    print OUT "Email id: nbendre\@clemson.edu   gjape\@clemson.edu****************\n";
    print OUT "******************************************************************\n";
    print OUT "**TIME ::\t     " . localtime() ."\t          |\n";
    print OUT "******************************************************************\n\n";
}

sub displayInfo1
{
	#open (OP, ">$outFile") or die "Error: Cannot open file: $!\n";
    print OP "******************************************************************\n";
    print OP "*********************** NIKHIL BENDRE & GAURI JAPE ****************\n";
    print OP "******************************************************************\n";
    print OP "Email id: nbendre\@clemson.edu   gjape\@clemson.edu****************\n";
    print OP "******************************************************************\n";
    print OP "**TIME ::\t     " . localtime() ."\t          |\n";
    print OP "******************************************************************\n\n";
}
sub displayInfo2
{
	#open (OP, ">$outFile") or die "Error: Cannot open file: $!\n";
    print SEM "******************************************************************\n";
    print SEM "*********************** NIKHIL BENDRE & GAURI JAPE ****************\n";
    print SEM "******************************************************************\n";
    print SEM "Email id: nbendre\@clemson.edu   gjape\@clemson.edu****************\n";
    print SEM "******************************************************************\n";
    print SEM "**TIME ::\t     " . localtime() ."\t          |\n";
    print SEM "******************************************************************\n\n";
}
sub readarr
{
	open(CON1,'<',"testArr.txt") || die("Can't open file testArr.txt");
	my $i=0;

	my $j;
	while($line1 = <CON1>)
	{
	chomp($line1);
	@tmparray = split(//,$line1);

	for($j=0;$j<110;$j++)
	{
	$matrix[$i][$j]=$tmparray[$j];	
	}
	$i++;
}
 close(CON1);
}

sub prodList
{
	
	my($prodCheck)=$_[0];
	my $tmpProdCnt;
	
	open(CON5,'<',"productionlist.txt") || die("Can't open file testArr.txt");
	my $i=0;

	my $j;
	$tmpProdCnt=1;
	
	while($prodLine = <CON5>)
	{
		if($tmpProdCnt==$prodCheck)
		{
			$prodLine1 = $prodLine;
			print OP $prodLine;
		}
		
		$tmpProdCnt++;	
	}
 close(CON5);
}



sub readProd
{
   my @tmp1;
   my @difference;
   my $i;
   my $str;
   my @tmp;
   my $tmpStackCnt;
   
    $popdContentsAraay1="";  
    $cou=1;
    
    for($rit=$rit1;$rit<=$stack_cnt;$rit++)
   {
       $CLEMhandle=($cou).$popdContentsAraay1." ".$stack[$rit];
       $popdContentsAraay1=$popdContentsAraay1." ".$stack[$rit];
       $cou++;
       
   }  
	open(CON2,'<',"prodArray.txt") || die("Can't open file testArr.txt");
	$line2Cnt=1;
	
	
	while($line2 = <CON2>)
	{
		
		
		chomp($line2);
		$str=$line2;
		@tmparray1 = split(' ',$line2);
		$last_element= pop(@tmparray1);
	    
	    $handlewdoutright = join " ",@tmparray1;
		
		if($handlewdoutright =~ /(\A)^($CLEMhandle)/)
		{
			
			#printing normal reductions
			if($mainFlag[7]==1)
			{
			print OP "\n\t REDUCTION #$line2Cnt:";
			
			}
			prodList($line2Cnt);
			
			
			#Stack before reductio
			if($mainFlag[8]==1)
			{
				print OP "\n\t\t Stack BEFORE REDUCTION: @stack ";
			}
			
			$handleNotFound=1;
			$popCnt=$cou-1;
			## push in the $lst_element in the stack
			
			
				#saving the state of the Semantic Stack before Reduction
				@BeforeSemanticStack=();
				push(@BeforeSemanticStack,@semanticStack);
			
			$sempopCnt = $popCnt;
			
			while($popCnt!=0)
			{
				
				#
				pop(@stack);
				$stack_cnt--;
				$stack_top--;
				$popCnt--;
				
			
			
						
			#	pop(@semanticStack);
			#	$semanticStack_cnt--;
			#	$semanticStack_top--;
				
			}
			if($popCnt==0)
			{
				push(@stack,$last_element);
				$stack_cnt++;
				$stack_top++;
				
				#push into the semantic stack the enire string of symbols
					#push in semantic stack also
				
				
		if(@sem_list != () )
		{
				@procHeadList = @sem_list;
				$procHead = join " ",@procHeadList;
				
				#CHECK FOR PROGRAM NAME for production 2
				if($progNameSetFlag==1)
				{
					
					push(@globalSymbolTable,$sem_list[0]);
					
					$globalSymbol_cnt++;
					$globalSymbol_top++;
					$progNameSetFlag=0;
					
					@sem_list=();
					
				}
				#Check for PROCEDURE
				if($checkProcFlag==1)
				{
					$procName = shift(@sem_list);
					$procName = $procName.":"."PROCEDURE";
					push(@globalSymbolTable,$procName);
					$globalSymbol_cnt++;
					$globalSymbol_top++;
					$sem9=1;
				}	
				if($sem_list[0] eq 'INTEGER' || $sem_list[0] eq 'REAL' || $sem_list[0] eq 'STRING')
				{
				$sem_input = join ':',@sem_list;
				my $sem_input1 = $sem_input;
				@sem_input1	= split(':',$sem_input1);
				
				my $temp;
				$temp = $sem_input1[0];
				$sem_input1[0]= $sem_input1[1];
				$sem_input1[1]= $temp;
				$sem_input2 =join ':',@sem_input1;
				
				#semantics($line2Cnt);				
				# Error Checking here ?
				
				
				if($checkProcFlag==1)
				{
					push(@local_sem_list,$sem_input);
				}
				
				$checkSemanticError=1;
				
				} #to check if to add in globalsymbol table or not
				@sem_list=(); 
				
				
				#if($mainFlag[15]==1)
			    #{
				#     printSymbolTable();
			    #}	
			} #end if for semlist!=()
				
				#for local symbol table
				if($checkProcFlag==1)
				{
				
				@new1 = split (':',$local_sem_list[0]);
				while(@new1!=())
    			{
    				if($new1[0] eq "INTEGER"||$new1[0] eq "REAL"||$new1[0] eq "STRING")
    				{
   			 			   push(@lst,$new1[0]);
    					   shift(@new1);
      					   while($new1[0] ne "INTEGER" && $new1[0] ne "REAL" && $new1[0] ne "STRING" && @new1!=())
      					   {
  						    	push(@lst,$new1[0]);
        						shift(@new1);
        						$temp123 = join ':', @lst;
      					   }
      					   $sem12proc=1;
    				} ##----   
    			
    			$sem_input = join ':',@lst;
				my $sem_input1 = $sem_input;
				my @sem_input1	= split(':',$sem_input1);
				my $temp;
				$temp = $sem_input1[0];
				$sem_input1[0]= $sem_input1[1];
				$sem_input1[1]= $temp;
				my $sem_input2 =join ':',@sem_input1;
    					
      				push(@new2,$sem_input2);
      				@lst=();
    			}	
 				
 				#inserting it into local symbol table
 				#inserting the proc name
 				push(@localSymbolTable,$procName);
 				$localSymbol_top++;
				$localSymbol_cnt++;
				@local_sem_list=();
 				
 				#rest of elements
 				while($#new2+1)
 				{
 					push(@localSymbolTable,shift(@new2));
 					$localSymbol_top++;
 					$localSymbol_cnt++;
 					
 				}			
				
				#push(@localSymbolTable,$sem_input2);
				#$localSymbol_top++;
				#$localSymbol_cnt++;
				
				#$checkProcFlag=0;
				
				}#end if for $checkproc
				
				$checkProcFlag=0;
				
			} #if popcnt==0
				
			semantics($line2Cnt);
			
			while($sempopCnt!=0)
			{
				if($sempopFlag!=1 || $line2Cnt==118)
				{
				pop(@semanticStack);
				$semanticStack_cnt--;
				$semanticStack_top--;
				
				}
				$sempopCnt--;
			}
			if($checkSemanticError==1)
			{
			#-------------------------SEMANTIC ERROR CONDITION-----------------------
			#check Semantic errors ( Static Scooping of Variable's)
			#take the last element of the globalsymbol table and then iterate through
			my @globalTemp;
			my @globalTemp1;
			my $semCntErrors=0;
			my $s1;
			my $s2;
			
			push(@globalTemp,@globalSymbolTable);
			while(@globalTemp!=())
			{
			@globalTemp1= split(':',$globalTemp[0]);
			push(@checkSemErrors,$globalTemp1[0]);
			$semCntErrors++;
			shift(@globalTemp);
			}
			#actual check for error
			if($semCntErrors>1)
			{
				$s1=$semCntErrors-1;
				$s2=$s1-1;
				while($s2>=0)
				{
				if($checkSemErrors[$s1] eq $checkSemErrors[$s2])
				{
						print SEM "\n\t\t ********VARIABLE DECLARED ALREADY!******** \n";
						pop(@globalSymbolTable);
				}
				$s2--;
				}
					#$semCntErrors--;
					
					
			}
			@globalTemp=();
			@checkSemErrors=();
			$checkSemanticError=0;
			#---------------END of ERROR CONDITION------------------------------
			} #end of if 
			
			
			if($mainFlag[15]==1)
			{
			     printSymbolTable();
			}
			
			
			#print the top of stack, input and relation
			if($mainFlag[9]==1)
			{
				print OP "\n\t\t Stack Top : $stack[$stack_top] ";
				print OP "\n\t\t Input : $lexarray[$lex_cnt+1] ";
				print OP "\n\t\t Relation: GREATER THAN ";
			}
			#print the symbolic handle
			if($mainFlag[10]==1)
			{
				print OP "\n\t\t Symbolic Handle : $CLEMhandle ";
			}
			
			#print the Symbolic stack after and before reduction
			if($mainFlag[8]==1)
			{
				print OP "\n\t\t Stack AFTER REDUCTION: @stack ";
			}
			
			$printRed++;
			last;
		}
		$line2Cnt++;
		
	} #end of while
	
	
	if($handleNotFound==0)
	{
       $rit1++;
       readProd();
    }
	#@localSymbolTable=();
				#@localSymbolTable1=();
	close(CON2);
} #end sub	
sub commentfn
{   
	
	my($line)=$_[0];
	my $z;
	
	if($line =~m/^\s*\/\*/g)
	{ 
		$cmtflag=1;
		#print OUT "\t\tComment Line\n";
		
			 while($cmtflag)
			{
		    	if($line=~m/\*\//g)
				{
					$cmtflag=0;
					$count++;
					main($count);
				}
				else
				{
					$count++;
					main($count);
				}
				
			}
	}
	
	if($line=~m/\*\//g)
	{
		$cmtflag=0;
		$count++;
		main($count);
	}
				
}
sub iden
{
	if($cmtflag==0)
	{
	my ($line)=$_[0];
	my $z;

    
	if($line=~s/^([a-z][a-z0-9_-]*)//)
	{
		$z=$&;
		push(@sem_list,$z); 	#stored iden in list
		push(@sem_list2,$z);
		$sem_iden = $z;
		push(@iden_list,$z);
		
		push(@toVerifySemErrors,$z);
		
		my $x;
		$x=length($z);
		if($x > 16)
		{
			if($mainFlag[1]==1 && $mainFlag[2]==1)
			{
			print OUT "\nINVALID IDENTIFIER  $z IDENTIFIERS SHOULD BE AT THE MOST 16 CHARACTERS of the form [a-z][a-z0-9_-]* ";
			}
		}
		else
		{
			if($mainFlag[1]==1 && $mainFlag[2]==1)
			{
				print OUT "\n\t\t\t TOKEN: $z CODE: 56 ";
				push(@lexarray,56);
				push(@printArray,$z);
			}
			
		}
		#parser();
		if($line=~s/^\n//)
		{
			$count++;
			main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		
		$line=~s/^\s+//;
		lex($line);
		}
	} #end if	
}
sub realfn
{
	if($cmtflag==0)
	{
	my ($line)=$_[0];
	my $z;
	
	
	if($line=~s/(\A)^(\d+)\.(\d+)// || $line=~s/(\A)^\+(\d+)\.(\d+)// || $line=~ s/(\A)^\-(\d+)\.(\d+)//)
	{
		$z=$&;
		#@sem_list = $z; #Store real in list
		push(@sem_list,$z);
		push(@real_list,$z);
		my @r=$z;
		
		if(length($z) > 9)
		{
			if($mainFlag[1]==1 && $mainFlag[2]==1)
			{
			print OUT "\n\t INVALID REAL $z. The number has more than 7 significant digits. ";
			}	
		}
		
		else
		{
			if($mainFlag[1]==1 && $mainFlag[2]==1)
			{
				print OUT "\n\t\t\t TOKEN: $z CODE: 108 ";
				
				push(@lexarray,108);
				push(@printArray,$z);
			}
		}
		if($line=~s/^\n//)
		{
			$count++;
			main($count)
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line=~s/^\s+//;
		lex($line);
	}
	
	} #end if for checking comment flag
}

sub integerfn
{
	if($cmtflag==0)
	{
    my ($line)=$_[0];
    my $z;
   
    if($line=~s/(\A)^(\d+)// || $line =~ s/(\A)^\+(\d+)// || $line=~ s/(\A)^\-(\d+)//)
    {
        $z=$&;
        push(@sem_list,$z); #integer stored in list 
        push(@sem_list2,$z);
        push(@int_list,$z);
        
        my $x;
        $x=length($z);
        if($x>9)
        {
        	if($mainFlag[1]==1 && $mainFlag[2]==1)
        	{
        	print OUT "\n\t INVALID INTEGER. NUMBER GREATER than 9.\n"
        	}
        }
        else
        {
        	if($mainFlag[1]==1 && $mainFlag[2]==1)
        	{
        	print OUT "\n\t\t\t TOKEN $z CODE: 60 ";
        	push(@lexarray,60);
    		push(@printArray,$z);
    	   	}
        }
        
        if($line=~s/^\n//)
        {
            $count++;
            main($count)
        }
        if($line eq '')
        {
            $count++;
            main($count);
        }
        $line=~s/^\s+//;
        lex($line);
    }
}# end if 
}
sub asc
{
	if($cmtflag==0)
	{
	my($line)=$_[0];
	my $z;
	
	if($line=~s/^\;//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
			
			print OUT "\n\t\t\t TOKEN: $z CODE: 58";
		    push(@lexarray,58);
		    push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\+//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
			print OUT "\n\t\t\t TOKEN: $z CODE: 104";
			push(@lexarray,104);
			push(@printArray,$z);
		
			push(@sem_list2,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\-//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
			print OUT "\n\t\t\t TOKEN: $z CODE: 105";
			push(@lexarray,105);
			push(@printArray,$z);
		
			push(@sem_list2,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\*//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 106";
		push(@lexarray,106);
		push(@printArray,$z);
		
		push(@sem_list2,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\///)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1) 
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 107";
		push(@lexarray,107);
		push(@printArray,$z);
		
		push(@sem_list2,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\=//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 59";
		push(@lexarray,59);
		push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\{//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 73";
		push(@lexarray,73);
		push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\}//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 71";
		push(@lexarray,71);
		push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\://)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 80";
		push(@lexarray,80);
		push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\!//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 97";
		push(@lexarray,97);
		push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\>//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 100";
		push(@lexarray,100);
		push(@printArray,$z);
		}
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\<//)
	{
		$z=$&;
		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
		print OUT "\n\t\t\t TOKEN: $z CODE: 98";
		push(@lexarray,98);
		push(@printArray,$z);
		}
		
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\)//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 87";
		push(@lexarray,87);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\(//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 86";
		push(@lexarray,86);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\[//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 78";
		push(@lexarray,78);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\]//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 79";
		push(@lexarray,79);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		elsif($line=~s/^\,//)
		{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 74";
		push(@lexarray,74);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	
	
	#elsif($line=~s/^\_//)
	#{
	#	$z=$&;
	#	push(@lexarray,);
	#	if($line=~s/^\n//)
	#	{
	#	$count++;
	#	main($count);
	#	}
	#	if($line eq '')
	#	{
	#		$count++;
	#		main($count);
	#	}
	#	$line =~s/^\s+//;
	#	lex($line);
	#}
	
	elsif($line=~s/^\.//)
	{
		$z=$&;
		print OUT "\n INVALID ASCII character.";
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\~//)
	{
		$z=$&;
		print OUT "\n INVALID ASCII Character.";
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\%//)
	{
		$z=$&;
		print OUT "\n INVALID ASCII Character $z.";
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\@//)
	{
		$z=$&;
		print OUT  "\n INVALID ASCII Character $z.";
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	elsif($line=~s/^\|//)
	{
		$z=$&;
		print OUT "\n INVALID ASCII Character $z.";
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	}#end if
	
}
sub multAsc
{
	if($cmtflag==0)
	{
	my($line)=$_[0];
	my $z;
	
	if($line=~s/^==//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 102";
		push(@lexarray,102);
		push(@printArray,$z);
		
		push(@sem_list2,$z);
		
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	if($line=~s/^!=//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 103";
		push(@lexarray,103);
		push(@printArray,$z);
		push(@sem_list2,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	if($line=~s/^<=//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 99";
		push(@lexarray,99);
		push(@printArray,$z);
		
		push(@sem_list2,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	if($line=~s/^>=//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 101";
		push(@lexarray,101);
		push(@printArray,$z);
		push(@sem_list2,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	
	if($line=~s/^<-//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 93";
		push(@lexarray,93);
		push(@printArray,$z);
		push(@sem_list2,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
		
	if($line=~s/^&&//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 96";
		push(@lexarray,96);
		push(@printArray,$z);
		
		push(@sem_list2,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	if($line=~s/^,,//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 109";
		push(@lexarray,109);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	if($line=~s/^,\://)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 80";
		push(@lexarray,80);
		push(@printArray,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	
	if($line=~s/^\|\|//)
	{
		$z=$&;
		print OUT "\n\t\t\t TOKEN: $z CODE: 95";
		push(@lexarray,95);
		push(@printArray,$z);
		
		push(@sem_list2,$z);
		if($line=~s/^\n//)
		{
		$count++;
		main($count);
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	}#endif
}

sub chckResv
{
	
	if($cmtflag==0)
	{
	my($line)=$_[0];
	my $z;
	my $resvFlag=0;
	
	if($line=~s/(\A)^[A-Z]+//)
	{
		$z = $&;
		
		if($z eq 'IF')
		{
			if($mainFlag[1]==1 && $mainFlag[2]==1)
			{
			print OUT "\n\t\t\t TOKEN: $z CODE: 85";
			push(@lexarray,85);
			push(@printArray,$z);
			}
			
			$resvFlag=1;
		}
		
		elsif($z eq 'END')
		{
			if($mainFlag[1]==1 && $mainFlag[2]==1)
			{
			print OUT "\n\t\t\t TOKEN: $z CODE: 54";
			push(@lexarray,54);
			push(@printArray,$z);
			$checkSemanticError=1;
			}
			$resvFlag=1;
		}
		
		elsif($z eq 'PROGRAM')
		{
			print OUT "\n\t\t\t TOKEN: $z CODE: 55";
			push(@lexarray,55);
			push(@printArray,$z);
			$progNameSetFlag=1;
			$resvFlag=1;
		}
		
		
		elsif($z eq 'DECLARE')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 57";
            	push(@lexarray,57);
            	push(@printArray,$z);
            $resvFlag=1;
        } 
               
		elsif($z eq 'CHARACTERS')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 61";
            	push(@lexarray,61);
				push(@printArray,$z);       
				push(@sem_list,'CHARACTERS');     
            $resvFlag=1;
        } 
		elsif($z eq 'VECTOR')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 62";
            push(@lexarray,62);
            push(@printArray,$z);
            push(@sem_list,$z);
            $resvFlag=1;
        } 
		elsif($z eq 'ELEMENTS')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 63";
            push(@lexarray,63);
            push(@printArray,$z);
            $resvFlag=1;
        }                 
		elsif($z eq 'EACH')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 64";
            	push(@lexarray,64);
            	push(@printArray,$z);
            	push(@sem_list,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'MATRIX')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 65";
            	push(@lexarray,65);
            	push(@printArray,$z);
            	push(@sem_list,'MATRIX');
            $resvFlag=1;
            $matrixWord=1;
            
        }         
		elsif($z eq 'MAIN')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 77";
            	push(@lexarray,77);
            	push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'INPUT')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 81";
            	push(@lexarray,81);
            	push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'ROWS')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 66";
            	push(@lexarray,66);
            	push(@printArray,$z);
            	
            $resvFlag=1;
        }         
		elsif($z eq 'COLUMNS')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 67";
            	push(@lexarray,67);
            	push(@printArray,$z);
            $resvFlag=1;
        } 
		elsif($z eq 'REAL')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 69";
            	push(@lexarray,69);
            	push(@printArray,$z);
            	push(@sem_list,'REAL');
            $resvFlag=1;
            			
        } 
		elsif($z eq 'INTEGER')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 68";
            	push(@lexarray,68);
            	push(@printArray,$z);
            	push(@sem_list,$z);
          	  $resvFlag=1;
        }         
		elsif($z eq 'STRING')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 70";
              	push(@lexarray,70);
              	push(@printArray,$z);
              	push(@sem_list,$z);
	
            $resvFlag=1;
        }         
		elsif($z eq 'PROCEDURE')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 72";
              	push(@lexarray,72);
              	push(@printArray,$z);
            $resvFlag=1;
            $checkProcFlag=1;
        }         
		elsif($z eq 'VALUE')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 75";
              	push(@lexarray,75);
              	push(@printArray,$z);
              	#push(@sem_list,$z);
            $resvFlag=1;
        } 
		elsif($z eq 'REFERENCE')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 76";
              	push(@lexarray,76);
              	push(@printArray,$z);
              	#push(@sem_list,$z);
            $resvFlag=1;
        } 
		elsif($z eq 'OUTPUT')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 82";
              	push(@lexarray,82);
              	push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'CALL')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 83";
              	push(@lexarray,83);
              	push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'ELSE')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 84";
              	push(@lexarray,84);
              	push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'THEN')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 88";
              	push(@lexarray,88);
              	push(@printArray,$z);
            $resvFlag=1;
        }
		elsif($z eq 'DO')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 91";
            push(@lexarray,91);
            push(@printArray,$z);
            $resvFlag=1;
        } 
		elsif($z eq 'INCREMENT')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 89";
            push(@lexarray,89);
            push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'BY')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 90";
            push(@lexarray,90);
            push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'FOR')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 92";
            push(@lexarray,92);
            push(@printArray,$z);
            $resvFlag=1;
        }         
		elsif($z eq 'UNTIL')
        {
            print OUT "\n\t\t\t TOKEN: $z CODE: 94";
            push(@lexarray,94);
            push(@printArray,$z);
            $resvFlag=1;
        }
    
    	          
		if($resvFlag==0)
		{
			print OUT "\n INVALID RESERVED WORD:: $z ";
		}
		if($line=~s/^\n//)
		{
    		$count++;
	    	
	    	main($count);
	    	
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		$line =~s/^\s+//;
		lex($line);
	}
	
	} #end of if condition
	
}
sub singleComment
{
	if($cmtflag==0)
	{
		my($line)=$_[0];
		
		if($line=~/^\s*\/\/.*/g)
		{
			$singleCmtflag=1;
			$count++;
			main($count);
		}
		if($line=~s/^\n//)
		{
    		$count++;
	    	
	    	main($count);
	    	
		}
		if($line eq '')
		{
			$count++;
			main($count);
		}
		
		
	}	
}
sub stringFn
{
	my $str1;
	my $str2;
	my $stringContinue=0;
	if($cmtflag==0)
	{
	my ($line)=$_[0];
	
	if($line=~/^\".*?\"/)
	{
		
		$str1=$&;
		@sem_list = $str1;
		
		$str2=$';

		if($mainFlag[1]==1 && $mainFlag[2]==1)
		{
			print OUT "\nString Token: $str1";
		}
		$stringContinue=1;
		
		$line=$str2;
	}
	if($line=~s/^\n//)
	{
    		$count++;
	    	main($count);
	}
	if($line eq '')
	{
			$count++;
			main($count);
	}
		if($stringContinue==1)
		{
		lex($line);
		}
	}
	
}
sub chckflag
{
my ($line)=$_[0];
 my $z;
 my $y;
 my $a;
 my $b;
 
  if($line=~s/^##//)
  {
     $z=$_[0];
     while($line=~s/^\+//)
     {
        if($line=~s/^(\A)^(\d+)//)
         {
             $a=$&;
             $mainFlag[$a]=1;
             print OUT "\n\t\t\t FLAG $a is SET ON";
         }
     }    
 	 while($line=~s/^\-//)
     {
      	   if($line=~s/^(\A)^(\d+)//)
      		{
              my $b=$&;
              $mainFlag[$b]=0;
              print OUT "\n\t\t\t FLAG $b is SET OFF";
    		}
     }
      $count++;
      main($count);
     
   }
       
      	    
	    if($line=~s/^\n//)
        {
            $count++;
            main($count);
        }
        if($line eq '')
        {
            $count++;
            main($count);
        }
        $line=~s/^\s+//;
      
}

sub lex
{		
		$x = $_[0];
		commentfn($x);
		singleComment($x);
		stringFn($x);
		chckflag($x);
		realfn($x);
		integerfn($x);
		chckResv($x);
		multAsc($x);
		asc($x);
		iden($x);
}
sub updateTuple
 {
  
  	if($mainFlag[14]==1)
  	{  
     my $var1 = shift;
     my $var2 = shift;
     my $var3 = shift;
     my $var4 =shift;
    
    @tupleRow=join ',',$var1,$var2,$var3,$var4;
    
    push(@tuple,@tupleRow);
     
    print SEM "\n\t\t Tuple is : (@tupleRow) \n ";
    
  	}
  	 
    
 }
sub semantics
{
	my ($semanticNum)=$_[0];
	my $rhs = $prodLine1; # direct string
	my $s1;
	my $var = $last_element;
	#my $lhs = $rev_token{$var};
	my $lhs = $semanticStack[$semanticStack_top];
	my @rhs1 = split ' ',$rhs;
	my $temp1;
	my @tempZ;
	
	#1
	if($semanticNum==1)
	{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$globalSymbolTable[0]","ENDPROGRAM","-","-");
		
		$sempopFlag=0;
		
		
	}
	
	#for production 2 which is prog -> PROGRAM var
	if($semanticNum==2)
	{
		push(@semanticStack,$globalSymbolTable[$globalSymbol_cnt-1]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","PROGRAMBEGIN","-","-");
		@sem_list=();
		$sempopFlag=0;
	}

	#for 'lambada' production in betwn 1-18
	if($semanticNum==3 || $semanticNum==4 || $semanticNum==6 || $semanticNum==7 || $semanticNum==8)
	{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$sempopFlag=0;
	}
	
	#for production 5 declpart -> DECLARE declist END
	if($semanticNum==5)
	{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("-","ENDDECLARATION","-","-");
		$sempopFlag=0;
	}
	
	
	
	#for production 9 declstat  --> type  var
	if($semanticNum==9)
	{
		if($procFlag==0 && $sem9==0)
		{
		#push into global stack
		$sem_input2 = $sem_input2.":"."SCALAR".":"."0".":"."0";
		push(@globalSymbolTable,$sem_input2);
		$globalSymbol_cnt++;
		$globalSymbol_top++;
		@sem_list=();
		}
		else
		{
		$sem_input2 = $sem_input2.":"."SCALAR".":"."0".":"."0";
		push(@localSymbolTable1,$sem_input2);
		$localSymbol_cnt++;
		$localSymbol_top++;
		@sem_list=();
		}
		
		#push into semantic stack
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","MEMORY","4","-");
		$sempopFlag=0;
		
	}
	
	
	 
	
	
	
		#for production 10
	if($semanticNum==10)
	{
		
		updateTuple("$semanticStack[$semanticStack_cnt-2]","INTIALMEMORY","4","$semanticStack[$semanticStack_top]");
		$sempopFlag=0;
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
	}
	
	
	
	#for production 11
	if($semanticNum==11)
	{
		
		my @temp11 = split(':',$sem_input2);
		my $val11 = $temp11[2];
		
		my $temp11;
		$sem_input11[1]=$sem_input11[1].":"."0".":"."0";
		$temp11= join "|",@sem_input1;
			
		#push into global stack
		
		
		push(@globalSymbolTable,$temp11);
		$globalSymbol_cnt++;
		$globalSymbol_top++;
		@sem_list=();
		
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","MEMORY","$val11","-");
		$sempopFlag=0;
	}
	
	#12
	if($semanticNum==12)
	{
		my @temp12;
		my $row12;
		my $col12;
		my $const12=4;
		
		my $ans12;
		
		@temp12 = split(':',$sem_input2);
		$row12 = $temp12[3];
		
		$ans12 = ($row12 * $const12); 
		
		#if($procFlag==0)
		#if($checkProcFlag==0)
		#{
		#push into global stack
		$sem_input2 = $sem_input2.":"."0";
		push(@globalSymbolTable,$sem_input2);
		$globalSymbol_cnt++;
		$globalSymbol_top++;
		@sem_list=();
		#}
		if($sem12proc==1)
		{
		$sem_input2 = $sem_input2.":"."0";
		push(@localSymbolTable1,$sem_input2);
		$localSymbol_cnt++;
		$localSymbol_top++;
		@sem_list=();
		pop(@globalSymbolTable); ##check later
		}
		#
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","MEMORY","$ans12","-");
		@temp12=();
		$sempopFlag=0;
		
	}
	
	#for production 13
	if($semanticNum==13)
	{
		my @temp13;
		my $row13;
		my $col13;
		my $const13=4;
		
		my $ans13;
		
		@temp13 = split(':',$sem_input2);
		$row13 = $temp13[3];
		$col13 = $temp13[5];
		$ans13 = ($row13 * $col13); 
		
		
		my $temp13;
		
		$sem_input13[3]=$sem_input13[3].":"."0";
		$temp13= join "|",@sem_input1;
		#push into global stack
		push(@globalSymbolTable,$temp13);
		$globalSymbol_cnt++;
		$globalSymbol_top++;
		@sem_list=();
		
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","MEMORY","$ans13","-");
		$sempopFlag=0;
	}

	#for production 14
	if($semanticNum==14)
	{
		my @temp14;
		my $row14;
		my $col14;
		my $const14=4;
		
		my $ans14;
		
		@temp14 = split(':',$sem_input2);
		$row14 = $temp14[3];
		$col14 = $temp14[4];
		$ans14 = ($row14 * $col14* $const14); 
		
		#push into global stack
		push(@globalSymbolTable,$sem_input2);
		$globalSymbol_cnt++;
		$globalSymbol_top++;
		@sem_list=();
		
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","MEMORY","$row14","$col14");
		$sempopFlag=0;
		
	}	
	
	#for production 15
	if($semanticNum==15)
	{
		my @temp15;
		my $row15;
		my $col15;
		my $ans15;
		my $char15;
		
		my $const15=4;
		@temp15 = split(':',$sem_input2);
		$row15 = $temp15[3];
		$col15 = $temp15[4];
		$char15 = $temp15[6];
		$ans15 = ($row15 * $col15 * $char15); 
		
		#push into global stack
		push(@globalSymbolTable,$sem_input2);
		$globalSymbol_cnt++;
		$globalSymbol_top++;
		@sem_list=();
		
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("$sem_iden","MEMORY","$ans15","-");
		$sempopFlag=0;
	}
	
	#for production 16 type -> INTEGER
	if($semanticNum==16)
	{
		if($procFlag==0)
		{
		push(@semanticStack,"integer");
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		}
		else
		{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		}
	}
	
	#for production 17 type -> REAL
	if($semanticNum==17)
	{
		if($procFlag==0)
		{
		push(@semanticStack,"real");
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		}
		else
		{
			push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		}
	}
	
	#for production 18 type -> STRING
	if($semanticNum==18)
	{
		if($procFlag==0)
		{
		push(@semanticStack,"string");
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		}
		else
		{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		}
	}
	
	
	
	#for 'lambda' production in betwn 19-42
	if($semanticNum==19 || $semanticNum==20 || $semanticNum==21 || $semanticNum==24 || $semanticNum==28)
	{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
	}
	
	#-----------------------------------19-42-----------------------------------------
	#22 or 23 
	if($semanticNum==22 || $semanticNum==23)
	{
		
		updateTuple("-","ENDPROCEDURE","-","-");
		
		if($mainFlag[14]==1)
				{
					printLocalSymTable();
				}
		$procFlag=0;
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		#@localSymbolTable=();
		@localSymbolTable1=();
		
		
	}
	
	
	#25 
	if($semanticNum==25)
	{
		push(@semanticStack,'-');
		$semanticStack_cnt++;
		$semanticStack_top++;
		updateTuple("-","ENDFORMALPARAMETERS","-","-");
		$procFlag=0;
		$sempopFlag=0;
	}
	
	#for production 26
	if($semanticNum==26)
	{
		
		$sempopFlag=0;
		updateTuple("$semanticStack[$semanticStack_top]","BEGINPROCEDURE","-","-");
		push(@semanticStack,$localSymbolTable[0]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$procFlag =1;
		#push(@localSymbolTable1,$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		$localSymbol_cnt++;
		$localSymbol_top++;
		#shift(@localSymbolTable);	
		#1.create a local symbol table
		#2.set the proc flag
		
		#push(@localSymbolTable,$globalSymbol_cnt-1);
		
		#$procFlag=1;
		
	}
	
	#27 
	if($semanticNum==27)
	{
		updateTuple("-","NO FORMAL PARAMETERS","-","-");
	}
	
	#29
	if($semanticNum==29)
	{
		$localSymbolTable[0] = $localSymbolTable[0]."VALUE/REFERENCE";
		@tempZ = split(':',$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[2].PARAMETER.MEMORY","$tempZ[1]","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
	}
	
	#30
	if($semanticNum==30)
	{
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE/REFERENCE";
		@tempZ = split(':',$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[4].PARAMETER.MEMORY","$tempZ[1]","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
	}
	
	#31 fparmlist- --> fparmlist- , calltype type var VECTOR integer ELEMENTS
	if($semanticNum==31)
	{
		my @temp31;
		my $row31;
		my $col31;
		my $const31=4;
		
		my $ans31;
		
		@temp31 = split(':',$localSymbolTable[0]);
		$row31 = $temp31[3];
		
		$ans31 = ($row31 * $const31); 
		#
		$localSymbolTable[0] = $localSymbolTable[0].":"."0".":"."0".":"."REFERENCE";
		@tempZ = split(':',$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[6].PARAMETER.MEMORY","$ans31","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
	}
	
	#32
	if($semanticNum==32)
	{
		my @temp32;
		my $row32;
		my $col32;
		my $const32=4;
		
		my $ans32;
		
		@temp32 = split(':',$localSymbolTable[0]);
		$row32 = $temp32[3];
		$col32 = $temp32[5];
		$ans32 = ($row32 * $col32); 
		
		
		#
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE/REFERENCE";
		@tempZ = split(':',$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[7].PARAMETER.MEMORY","$ans32","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
	}
	
	#33 
	if($semanticNum==33)
	{
		my @temp33;
		my $row33;
		my $col33;
		my $const33=4;
		
		my $ans33;
		
		@temp33 = split(':',$localSymbolTable[0]);
		$row33 = $temp33[3];
		$col33 = $temp33[4];
		$ans33 = ($row33 * $col33* $const33); 
		#
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE";
		@tempZ = split (':',$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		updateTuple("$tempZ[0]","FORMAL.$tempZ[5].PARAMETER.MEMORY","$ans33","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
	}
	
	#34
	
	if($semanticNum==34)
	{
		my @temp34;
		my $row34;
		my $col34;
		my $const34;
		
		my $ans34;
		
		@temp34 = split(':',$localSymbolTable[0]);
		$row34 = $temp34[3];
		$col34 = $temp34[4];
		$const34 = $temp34[6];
		
		$ans34 = ($row34 * $col34* $const34); 
		
		#
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE/REFERENCE";
		@tempZ = split(':',$localSymbolTable[0]);
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[8].PARAMETER.MEMORY","$ans34","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
	}
	
	#35 fparmlist- --> { calltype type var
	if($semanticNum==35)
	{
		updateTuple("-","BEGIN FORMAL PARAMETERS","-","-");
		#push(@localSymbolTable,$sem_input);
		#$localSymbol_cnt++;
		#$localSymbol_top++;
		
	
		$localSymbolTable[0] = $localSymbolTable[0].":"."SCALAR".":"."0".":"."0".":"."$semanticStack[$semanticStack_cnt-2]";	
		@tempZ = split(/:/,$localSymbolTable[0]);
		
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$semanticStack[$semanticStack_top]","FORMAL.$semanticStack[$semanticStack_cnt-2].PARAMETER.MEMORY","4","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
		
	}
	#36
	if($semanticNum==36)
	{
		my @temp36;
		my $row36;
		my $col36;
		my $const36=4;
		
		my $ans36;
		
		@temp36 = split(':',$localSymbolTable[0]);
 		$ans36 = $temp36[2];;
		
		#
		updateTuple("-","BEGIN FORMAL PARAMETERS","-","-");
	
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE";	
		@tempZ = split(/:/,$localSymbolTable[0]);
		
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[4].PARAMETER.MEMORY","$ans36","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
	}
	
	#37
	if($semanticNum==37)
	{
		my @temp37;
		my $row37;
		my $col37;
		my $const37=4;
		
		my $ans37;
		
		@temp37 = split(':',$localSymbolTable[0]);
		$row37 = $temp37[3];
		
		
		$ans37 = ($row37 * $const37);
		
		#
		updateTuple("-","BEGIN FORMAL PARAMETERS","-","-");
	
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE";	
		@tempZ = split(/:/,$localSymbolTable[0]);
		
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[4].PARAMETER.MEMORY","$ans37","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
		
	}
	#38
	if($semanticNum==38)
	{
		my @temp38;
		my $row38;
		my $col38;
		my $const38=4;
		
		my $ans38;
		
		@temp38 = split(':',$localSymbolTable[0]);
		$row38 = $temp38[3];
		$col38 = $temp38[5];
		
		$ans38 = ($row38 * $col38);
		
		#
		updateTuple("-","BEGIN FORMAL PARAMETERS","-","-");
	
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE";	
		@tempZ = split(/:/,$localSymbolTable[0]);
		
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[7].PARAMETER.MEMORY","$ans38","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
		
	}
	
	#39
	if($semanticNum==39)
	{
		my @temp39;
		my $row39;
		my $col39;
		my $const39=4;
		
		my $ans39;
		
		@temp39 = split(':',$localSymbolTable[0]);
		$row39 = $temp39[3];
		$col39 = $temp39[4];
		
		$ans39 = ($row39 * $col39* $const39);
		
		#
		updateTuple("-","BEGIN FORMAL PARAMETERS","-","-");
	
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE";	
		@tempZ = split(/:/,$localSymbolTable[0]);
		
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[5].PARAMETER.MEMORY","$ans39","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
		
		
	}
	#40
	if($semanticNum==40)
	{
		my @temp40;
		my $row40;
		my $col40;
		my $ans40;
		my $char40;
		
		my $const40=4;
		@temp40 = split(':',$localSymbolTable[0]);
		$row40 = $temp40[3];
		$col40 = $temp40[4];
		$char40 = $temp40[6];
		$ans40 = ($row40 * $col40 * $char40); 
		
		#push into global stack
		updateTuple("-","BEGIN FORMAL PARAMETERS","-","-");
	
		$localSymbolTable[0] = $localSymbolTable[0].":"."VALUE";	
		@tempZ = split(/:/,$localSymbolTable[0]);
		
		push(@localSymbolTable1,shift(@localSymbolTable));
		
		updateTuple("$tempZ[0]","FORMAL.$tempZ[8].PARAMETER.MEMORY","$ans40","-");
		@tempZ=();
		push(@semanticStack,$localSymbol_cnt-1);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		$localSymbol_cnt++;
		$localSymbol_top++;
	
	}
	
	
	#41 calltype -> VALUE
	if($semanticNum==41)
	{
		push(@semanticStack,"VALUE");
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
	}
	
	#42 calltype -> REFERENCE
	if($semanticNum==42)
	{
		push(@semanticStack,"REFERENCE");
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
	}
	
	#----------------------------------SEMANTIC2---------------------------------------------------------------------
		#for 'lambada' production in betwn 43-65
	if($semanticNum==43 || $semanticNum==45 || $semanticNum==46 || $semanticNum==47 || $semanticNum==48 || $semanticNum==49 )
	{
		$sempopFlag=1;
#		push(@semanticStack,'-');
#		$semanticStack_cnt++;
#		$semanticStack_top++;
	}
	
	##prod 44
	
	if($semanticNum==44)
	{
		updateTuple("MAIN","LABEL","-","-");
	}
	
	
	if($semanticNum==50 || $semanticNum==51 || $semanticNum==52 || $semanticNum==53) 
	{
		$sempopFlag=1;
#		push(@semanticStack,'-');
#		$semanticStack_cnt++;
#		$semanticStack_top++;
	}
	
	#prod 54
	
	if($semanticNum==54)
	{
		
		#2
		updateTuple("-","ACTUAL PARAMETERS","$semanticStack[$semanticStack_cnt]","-");
		updateTuple("-","END INPUT PARAMETERS","-","-");
			
		$sempopFlag=0;
	}
	
	#prod 60 
	if($semanticNum==60)
	{
		
		#2
		updateTuple("-","ACTUAL PARAMETERS","$semanticStack[$semanticStack_cnt]","-");
		
		
		
		updateTuple("-","END OUTPUT PARAMETERS","-","-");
		
		
		
		$sempopFlag=0;
	}
	
	
	
	#prod 55
	
	if($semanticNum==55)
	{
		
		#3
		updateTuple("-","ACTUAL SUB PARAMETERS","$semanticStack[$semanticStack_cnt]","I&$m");
		
		$m++;
	}
	
	#prod 61
	if($semanticNum==61)
	{
		
		#3
		updateTuple("-","ACTUAL SUB PARAMETERS","$semanticStack[$semanticStack_cnt]","I&$m");
		
		$m++;
	}
	
	#prod 56
	if($semanticNum==56)
	{
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		$semFoundCol = $semExtracted[4];
		
		#3
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt-3]","$semFoundCol");
		
		$l1 = $m+1;
		
		#4
		updateTuple("I&$l1","IADD","I&$m","$semanticStack[$semanticStack_cnt-1]");
		
		#5
		updateTuple("-","ACTUAL SUB PARAMETERS","$semanticStack[$semanticStack_cnt-5]","I&$l1");
		
		
		$m=$l1;
		$m++;
		$sempopFlag=0;
		
	}
	
	#prod 62
	if($semanticNum==62)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		$semFoundCol = $semExtracted[4];
		
		#3
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt-3]","$semFoundCol");
		
		$k1 = $m+1;
		#4
		updateTuple("I&$k1","IADD","I&$m","$semanticStack[$semanticStack_cnt-1]");
		
		#5
		updateTuple("-","ACTUAL SUB PARAMETERS","$semanticStack[$semanticStack_cnt-5]","I&$k1");
		
		$m=$k1;
		$m++;
		$sempopFlag=0;
		
	}
	#prod 57
	if($semanticNum==57)
	{
		#1
		updateTuple("-","PROCEDURE CALL","scanf","-");
		
		#2
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","$semanticStack[$semanticStack_cnt]","-");
		
		#3
		updateTuple("-","ACTUAL PARAMETERS","$semanticStack[$semanticStack_cnt]","-");
	
		$sempopFlag=0;
		
	}
	
	#prod 63
	if($semanticNum==63)
	{
		#1
		updateTuple("-","PROCEDURE CALL","printf","-");
		
		#2
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","$semanticStack[$semanticStack_cnt]","-");
		
		#3
		updateTuple("-","ACTUAL PARAMETERS","$semanticStack[$semanticStack_cnt]","-");
	
		$sempopFlag=0;
		
	}
	#prod 58 
	## get it confirmed
	
	if($semanticNum==58)
	{
		#1
		updateTuple("-","PROCEDURE CALL","scanf","-");
		
		#2
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-","-");
		
		#3
		updateTuple("-","ACTUAL SUB PARAMETERS INPUT","$semanticStack[$semanticStack_cnt-3]","$semanticStack[$semanticStack_cnt-1]");
		
		
	}
	
	
	
	if($semanticNum==64)
	{
		#1
		updateTuple("-","PROCEDURE CALL","printf","-");
		
		#2
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-","-");
		
		#3
		updateTuple("-","ACTUAL SUB PARAMETERS OUTPUT","$semanticStack[$semanticStack_cnt-3]","$semanticStack[$semanticStack_cnt-1]");
		
		
		
		#$sempopFlag=0;
	}
	
	
	#prod 59
	if($semanticNum==59)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		$semFoundCol = $semExtracted[4];
		#1
		updateTuple("-","PROCEDURE CALL","scanf","-");
		
		#2
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-");
		
		#3
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt-3]","$semFoundCol");
		
		$u1 = $m+1;
		
		#4
		updateTuple("I&$u1","IADD","I&$m","$semanticStack[$semanticStack_cnt-1]");
		
		#5
		updateTuple("-","ACTUAL SUB PARAMETERS INPUT","$semanticStack[$semanticStack_cnt-5]","I&$u1");
		
		$m=$u1;
		$m++;
	}
	
	
	#prod 65
	if($semanticNum==65)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		$semFoundCol = $semExtracted[4];
	
		#1
		updateTuple("-","PROCEDURE CALL","printf","-");
		
		#2
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-");
		
		#3
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt-3]","$semFoundCol");
		
		 $u2 = $m+1;
		
		#4
		updateTuple("I&$u2","IADD","I&$m","$semanticStack[$semanticStack_cnt-1]");
		
		#5
		updateTuple("-","ACTUAL SUB PARAMETERS OUTPUT","$semanticStack[$semanticStack_cnt-5]","I&$u2");
		
		$m=$u2;
		$m++;
	}
	
	
	#for 'lambada' production in betwn 66-82
	#prod 66
	if($semanticNum==66)
	{
		updateTuple("-","NO PARAMETERS","-","-");
		
	}
	
	#prod 67
	if($semanticNum==67)
	{
		updateTuple("-","END ACTUAL PARAMETERS LIST","-");
		$sempopFlag=0;
	}
	
	#prod 68
	if($semanticNum==68)
	{
		#check if the the var is a of the type procedure
		
		updateTuple("$semanticStack[$semanticStack_cnt]","PROCEDURE CALL","-","-");
		
		$sempopFlag=0;
	}
	if($semanticNum==69)
	{
		$sempopFlag=1;
		#push(@semanticStack,'-');
		#$semanticStack_cnt++;
		#$semanticStack_top++;
	}
	if($semanticNum==70)
	{
		#1
		#check weder subscripts are of type int
		my $subscript1IsInt1=0;
		 my $subscript1IsInt2=0;
		 
		#1
		#check the type of integer, if no then print error
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-1]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-1]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-1]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		$subscript1IsInt1 = $semINTFlag;
		
		
		#1
		#check the type of integer, if no then print error
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-3]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		$subscript1IsInt2 = $semINTFlag;
		
		#now compare whether they are 2 integers otherwise print error
		if($subscript1IsInt1!=1 || $subscript1IsInt2!=1)
		{
			#print SEM "\n \t SUBSCRIPT ERROR\n";
		}
		
				
		#4
		updateTuple("-","$semanticStack[$semanticStack_cnt-1] ACTUAL PARAMETERS","$semanticStack[$semanticStack_cnt]","-");
		$sempopFlag=0;
		
	}
	if($semanticNum==71)
	{
		#1
		#check weder its a int
		
				
		#4
		updateTuple("-","VALUE/REFERENCE ACTUAL SUB PARAMETERS","$sem_list2[$i1-1]","I&$(m+1)");
		
		$m++;
	}
	if($semanticNum==72)
	{
				
		#1
		#check weder its a int
		
		#2
		updateTuple("I&$m","IMULT","$sem_list2[$i1-1]","no of cols");
		
		#3
		updateTuple("I&$(m+1)","IADD","I&$m","$sem_list2[$i1]");
		
		#4
		updateTuple("-","VALUE/REFERENCE ACTUAL SUB PARAMETERS","$sem_list2[$i1-2]","I&$(m+1)");
		
		$m++;
	}
	if($semanticNum==73)
	{
		#0
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-","-");
		
		#1
		#check weder its a int
		
				
		#4
		updateTuple("-","$semanticStack[$semanticStack_cnt-1] ACTUAL PARAMETERS","$semanticStack[$semanticStack_cnt]","-");
		
		$sempopFlag=0;
		
	}
	if($semanticNum==74)
	{
		#0
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-","-");
		
		#1
		#check weder its a int
		
				
		#4
		updateTuple("-","VALUE/REFERENCE ACTUAL SUB PARAMETERS","$sem_list2[$i1-1]","I&$(m+1)");
		
		$m++;
	}
	if($semanticNum==75)
	{
		#0
		updateTuple("-","BEGIN ACTUAL PARAMETER LIST","-","-");
		
		#1
		#check weder its a int
		
		#2
		updateTuple("I&$m","IMULT","$sem_list2[$i1-1]","no of cols");
		
		#3
		updateTuple("I&$(m+1)","IADD","I&$m","$sem_list2[$i1]");
		
		#4
		updateTuple("-","VALUE/REFERENCE ACTUAL SUB PARAMETERS","$sem_list2[$i1-2]","I&$(m+1)");
		
		$m++;
	}
	
	if($semanticNum==79)
	{
		#L$2,CJUMP,B$1,-
		
		if($semanticStack[$semanticStack_cnt-2]=~m/(B)/)
		{
		updateTuple("L&$m","CJUMP","$semanticStack[$semanticStack_cnt-2]","-");
		push(@storeIfLable,"L&$m");
		$m++;
		$sempopFlag=0;
		}
		else
		{
			print SEM "\n\t ***** ERROR: NOT A BOOLEAN EXPR IN IF **** \n";
		}
	}
	
	if($semanticNum==78)
	{
		#L$3,JUMP,-,-
		#L$2,LABEL,-,-
		
		updateTuple("L&$m","JUMP","-","-");
		updateTuple(shift(@storeIfLable),"LABEL","-","-");
		push(@storeIfLable,"L&$m");
		$m++;
		
		$sempopFlag=0;
	}
	
	if($semanticNum==77)
	{
		#L$3,LABEL,-,-
		updateTuple(shift(@storeIfLable),"LABEL","-","-");
		
		$sempopFlag=0;
	}
	
	if($semanticNum==76)
	{
		updateTuple(shift(@storeIfLable),"LABEL","-","-");
		
		$sempopFlag=0;
	}
	
	
	
	if($semanticNum==82)
	{
		updateTuple("$semanticStack[$semanticStack_cnt-3]","STORE","$semanticStack[$semanticStack_cnt-1]","-");
		updateTuple("L&$m","LABEL","-","-");
		
		push(@storeForLabel,"L&$m");
		$m++;
		
		$sempopFlag=0;
	}
	
	if($semanticNum==81)
	{
		if($semanticStack[$semanticStack_cnt-2]=~m/(B)/)
		{
			updateTuple("L&$m","CJUMP","$semanticStack[$semanticStack_cnt-2]","-");
			push(@storeForLabel,"L&$m");
			$m++;
			$sempopFlag=0;
		}
		else
		{
			print SEM "\n\t **** ERROR: EXPRESSION NOT BOOLEAN IN FOR LOOP!! ****\n";
		}
		
	}
	
	
	if($semanticNum==80)
	{
		
		$countForLabels = $#storeForLabel;
		$pointLabels = $countForLabels;
		
		#updateTuple("I&$m","IADD","$semanticStack[$semanticStack_cnt-1]","$semanticStack[$semanticStack_cnt-3]");
		#updateTuple("$semanticStack[$semanticStack_cnt-3]","STORE","I&$m","-");
		updateTuple("$semanticStack[$semanticStack_cnt-3]","INCREMENT","$semanticStack[$semanticStack_cnt-1]","-");
		updateTuple("$storeForLabel[$pointLabels-1]","JUMP","-","-");
		updateTuple("$storeForLabel[$pointLabels]","LABEL","-","-");
		pop(@storeForLabel);
		pop(@storeForLabel);
		$pointLabels = $pointLabels - 2;
		$sempopFlag=0;
		#$m++;
		
	}
	
	
	
	#for 'lambada' production in betwn 83-104
	if($semanticNum==83 || $semanticNum==87 || $semanticNum==89 || $semanticNum==90 || $semanticNum==92)
	{
		$sempopFlag=1;
#		push(@semanticStack,'-');
#		$semanticStack_cnt++;
#		$semanticStack_top++;
	}
	
	if($semanticNum==84)
	{
		$chckConversion1=0;
		$chckConversion2=0;
		
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
				if($chckConversion1==0)
				{
					$chckConversion1=1;
				}
				else
				{
					$chckConversion2=1;
				}
			}
			
		}
		
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
				if($chckConversion1==0)
				{
					$chckConversion1=1;
				}
				else
				{
					$chckConversion2=1;
				}
			}
			
		}
		if($semREALFlag==1)
		{
			#convert int to real
			if($chckConversion1==0 && $chckConversion2==1)
			{
				updateTuple("R&$m","CONVERTITOR","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt] = "R&$m";
				$m++;
				
				updateTuple("$semanticStack[$semanticStack_cnt-2]","STORE","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt-2] = $semanticStack[$semanticStack_cnt];
				push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				
				$sempopFlag=0;
					
			}
			
			#convert real into int
			elsif($chckConversion1==1 && $chckConversion2==0)
			{
				updateTuple("R&$m","CONVERTRTOI","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt] = "I&$m";
				$m++;
				
				updateTuple("$semanticStack[$semanticStack_cnt-2]","STORE","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt-2] = $semanticStack[$semanticStack_cnt];
				push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				
				$sempopFlag=0;
				
			}
			#everything is real
			else
			{
				updateTuple("$semanticStack[$semanticStack_cnt-2]","STORE","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt-2] = $semanticStack[$semanticStack_cnt];
				push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				
				$sempopFlag=0;
			}
			
		}
		
		#everything is int
		else
		{
		updateTuple("$semanticStack[$semanticStack_cnt-2]","STORE","$semanticStack[$semanticStack_cnt]","-");
		$semanticStack[$semanticStack_cnt-2] = $semanticStack[$semanticStack_cnt];
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$sempopFlag=0;
		}
		
	}
	
	#prod 85
	if($semanticNum==85)
	{
		
		 $chckConversion1=0;
		 $chckConversion2=0;
		 
		#1
		#check the type of integer, if no then print error
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-5]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
				if($chckConversion1==0)
				{
				$chckConversion1=1;
				}
				else
				{
				$chckConversion2=1;
				}	
			}
		}
		
		
		
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
				if($chckConversion1==0)
				{
				$chckConversion1=1;
				}
				else
				{
				$chckConversion2=1;
				}	
			}
		}
		
		#now compare whether they are 2 integers otherwise print error
		if($semREALFlag==1)
		{
			if($chckConversion1==1 && $chckConversion2==0)
			{
				updateTuple("I&$m","CONVERSIONRTOI","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt] = "I&$m";
				$m++;
				updateTuple("$semanticStack[$semanticStack_cnt-5]","SUB STORE","$semanticStack[$semanticStack_cnt]","-");
				$semanticStack[$semanticStack_cnt-5] = $semanticStack[$semanticStack_cnt];
				push(@semanticStack,$semanticStack[$semanticStack_cnt-5]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				$sempopFlag=0;
				$m++;
			}
		}
		else
		{
			
		#5
		updateTuple("$semanticStack[$semanticStack_cnt-5]","SUB STORE","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-3]");
		
		#6
		$semanticStack[$semanticStack_cnt-5] = $semanticStack[$semanticStack_cnt];
		push(@semanticStack,$semanticStack[$semanticStack_cnt-5]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		
		}
	}
	#prod 86
	if($semanticNum==86)
	{
		$chckSub1=0;
		$chckSub2=0;
		 
		#1
		#check the type of integer, if no then print error
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-3]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		
		#1
		#check the type of integer, if no then print error
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-5]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#check that subscripts are INT
		if($chckSub2!=1)
		{
			print SEM "\n \t **** ERROR: SUBSCRIPTS ARE NOT INTEGERS ! \n\t ***** ";
		}
		
		
		#2 & 3
		#check the expr type with "var" and "aexpr"
		
				 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-7]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-7]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-7]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#storing the no of cols
		$semFoundCol = $semExtracted[4];
		
		
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt-5]","$semFoundCol");
		$v1=$m+1;
		
		#4
		updateTuple("I&$v1","IADD","I&$m","$semanticStack[$semanticStack_cnt-3]");
		
		#5
		updateTuple("$semanticStack[$semanticStack_cnt-7]","SUB STORE","$semanticStack[$semanticStack_cnt]","I&$v1");
		
	
		#6
		$semanticStack[$semanticStack_cnt-7] = $semanticStack[$semanticStack_cnt];
		
		push(@semanticStack,$semanticStack[$semanticStack_cnt-7]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$m=$v1;
		$m++;
		
		$sempopFlag=0;
		
		
		
	}
	
	#prod 88
	
	if($semanticNum==88)
	{
		#1
		#check the type of operands
		
		#2
		updateTuple("B&$m","OR","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
	
		#3
		$semanticStack[$semanticStack_cnt-2] = "B&$m";
		
		#push in semantic stack
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$m++;
	}
	
	#prod 91
	
	if($semanticNum==91)
	{
		#1
		#check the type of operands
		
		#2
		updateTuple("B&$m","AND","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
	
		#3
		$semanticStack[$semanticStack_cnt-2] = "B&$m";
		
		#push in semantic stack
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$m++;
	}
	
	#prod 94
	if($semanticNum==94)
	{
		#1
		#check if Boolean
		
		#2""
		updateTuple("B&$m","NOT","$semanticStack[$semanticStack_cnt]","-");
		
		#3
		$semanticStack[$semanticStack_cnt-1]= "B&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-1]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$m++;
		
		
	}
	
	#prod 97
	if($semanticNum==97)
	{
		#1 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
			updateTuple("B&$m","R LESS THAN ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
			$m++;
		
		}
		else
		{
			updateTuple("B&$m","I LESS THAN","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
			$m++;
			
		}
		
	}	
	#prod 98
	if($semanticNum==98)
	{
		#1 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
			updateTuple("B&$m","R LESS EQUALS ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$m++;
		
		}
		else
		{
			updateTuple("B&$m","I LESS EQUALS ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$m++;
			
		}
		$sempopFlag=0;
		
		
	}	
	#prod 99
	if($semanticNum==99)
	{
		#1 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
			updateTuple("B&$m","R GREATER THAN","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
			$m++;
		
		}
		else
		{
			updateTuple("B&$m","I GREATER THAN","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
			$m++;
			
		}
		
	}	
	
	#prod 100
	if($semanticNum==100)
	{
		#1 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
			updateTuple("B&$m","R GREATER EQUALS ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$m++;
		
		}
		else
		{
			updateTuple("B&$m","I GREATER EQUALS ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$m++;
			
		}
		
		
		
		
	}	
	#prod 101
	if($semanticNum==101)
	{
		#1 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			if($semanticStack[$semanticStack_cnt]=~m/I/)
			{
				$semINTFlag=1;
			}
			if($semLocalError==1 && $semGlobalError==1)
			{
				print SEM "\n\t **** ERROR: Variable $semanticStack[$semanticStack_cnt] has not been DEFINED!! **** \n"
			}
			
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			if($semanticStack[$semanticStack_cnt-2]=~m/I/)
			{
				$semINTFlag=1;
			}
			if($semLocalError==1 && $semGlobalError==1)
			{
				print SEM "\n\t **** ERROR: Variable $semanticStack[$semanticStack_cnt-2] has not been DEFINED!! ****\n "
			}
		}
		
		if($semREALFlag==1)
		{
			updateTuple("B&$m","R EQUALS ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
			$m++;
			
		
		}
		else
		{
			
			updateTuple("B&$m","I EQUALS ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
			$m++;
			
			
		}
		
	}	
	#prod 102
	if($semanticNum==102)
	{
		#1 
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
			updateTuple("B&$m","R NOT EQUAL ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$m++;
		
		}
		else
		{
			updateTuple("B&$m","I NOT EQUAL ","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
			$semanticStack[$semanticStack_cnt-2]="B&$m";
			push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$m++;
			
		}
		
		
	}	
	
	
	
	
	#for 'lambada' production in betwn 83-104
	if($semanticNum==93 || $semanticNum==95 || $semanticNum==96 || $semanticNum==103)
	{
		$sempopFlag=1;
#		push(@semanticStack,'-');
#		$semanticStack_cnt++;
#		$semanticStack_top++;
	}
	
	#for 'lambada' production in betwn 105-124
	if($semanticNum==105 || $semanticNum==109 || $semanticNum==110 || $semanticNum==113 || $semanticNum==114 || $semanticNum==119)
	{
		$sempopFlag=1;
#		push(@semanticStack,'-');
#		$semanticStack_cnt++;
#		$semanticStack_top++;
	}
	#for productions between 83-104
	
	

	if($semanticNum==106)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
		updateTuple("R&$m","RADD","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="R&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		else
		{
		updateTuple("I&$m","IADD","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="I&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		
		
	}
	
	if($semanticNum==107)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
		updateTuple("R&$m","RSUB","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="R&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		else
		{
		updateTuple("I&$m","ISUB","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="I&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		
	}
	
	if($semanticNum==108)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/(R)/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		if($semREALFlag==1)
		{
		updateTuple("R&$m","RSUB","0","$semanticStack[$semanticStack_cnt]");
		$semanticStack[$semanticStack_cnt-1]= "R&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-1]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		else
		{
		updateTuple("I&$m","ISUB","0","$semanticStack[$semanticStack_cnt]");
		$semanticStack[$semanticStack_cnt-1]= "I&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-1]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		
	}
	
	
	if($semanticNum==111)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		if($semREALFlag==1)
		{
		updateTuple("R&$m","RMULT","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="R&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		else
		{
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="I&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		
		
		
		
	}	


	if($semanticNum==112)
	{
		$chckConversion1=0;
		$chckConversion2=0;
		
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-2]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt-2]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
				if($chckConversion1==0)
				{
				$chckConversion1=1;
				}
				else
				{
				$chckConversion2=1;
				}	
				
			}
		}
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
				
				if($chckConversion1==0)
				{
					$chckConversion1=1;
				}
				else
				{
					$chckConversion2=1;
				}	
				
			}
			
		}
		
		
		
		if($semREALFlag==1)
		{
			if($chckConversion1==1 && $chckConversion2==0)
			{
				updateTuple("R&$m","CONVERSIONITOR","$semanticStack[$semanticStack_cnt-2]","-");
				$semanticStack[$semanticStack_cnt-2] = "R&$m";
				$m++;
				updateTuple("R&$m","RDIV","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
				$semanticStack[$semanticStack_cnt-2]="R&$m";
				$m++;
				push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				$sempopFlag=0;
			}
			elsif($chckConversion1==0 && $chckConversion2==1)
			{	
				updateTuple("R$m","CONVERSIONITOR","$semanticStack[$semanticStack_cnt-2]","-");
				$semanticStack[$semanticStack_cnt-2] = "R&$m";
				$m++;
				updateTuple("R&$m","RDIV","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
				$semanticStack[$semanticStack_cnt-2]="R&$m";
				push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				$m++;
				$sempopFlag=0;
			}
			else
			{
				updateTuple("R&$m","RDIV","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
				$semanticStack[$semanticStack_cnt-2]="R&$m";
				push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
				$semanticStack_cnt++;
				$semanticStack_top++;
				$m++;
				$sempopFlag=0;
			}
			
			
		}
		else
		{
		updateTuple("I&$m","IDIV","$semanticStack[$semanticStack_cnt]","$semanticStack[$semanticStack_cnt-2]");
		$semanticStack[$semanticStack_cnt-2]="I&$m";
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$m++;
		$sempopFlag=0;
		}
		
	}	

			
	if($semanticNum==115)
	{
		#(a) should change to (10)
		
		$semanticStack[$semanticStack_cnt-2] = $semanticStack[$semanticStack_cnt-1]; 
		push(@semanticStack,$semanticStack[$semanticStack_cnt-2]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		$sempopFlag=0;
		
	}
	
	
	if($semanticNum==116)
	{
		$chckSub1=0;
		$chckSub2=0;
		
		#check the subscripts
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-1]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-1]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/(R)/)
			{
				$semREALFlag=1;
				
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/(R)/)
			{
				$semREALFlag=1;
				
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		#check that subscripts are INT
		if($chckSub2!=1)
		{
			print SEM "\n \t **** ERROR: SUBSCRIPTS ARE NOT INTEGERS !\n\t **** ";
		}
		
		# get the no of cols from the var 
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-5]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/(R)/)
			{
				$semREALFlag=1;
				$NOTINTFLAG=1;
			}
			else
			{
				$semINTFlag=1;
			}
		}
		
		
		
		#get the col size from the semextracted array 
		$semFoundCol = $semExtracted[4];
		
		updateTuple("I&$m","IMULT","$semanticStack[$semanticStack_cnt-3]","$semFoundCol");
		
		#2.
		$p1=$m+1;
		updateTuple("I&$p1","IADD","I&$m","$semanticStack[$semanticStack_cnt-1]");
		
		$p2=$p1+1;
		#3. check if real or integer
		if($semREALFlag==1)
		{
			updateTuple("R&$p2","SUBLOAD","$semanticStack[$semanticStack_cnt-5]","R&$p1");
			$semanticStack[$semanticStack_cnt-5] = "R&$p2";
			$m=$p2;
			$m++;
			
			push(@semanticStack,$semanticStack[$semanticStack_cnt-5]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
		}
		else
		{
			updateTuple("I&$p2","SUBLOAD","$semanticStack[$semanticStack_cnt-5]","I&$p1");
			$semanticStack[$semanticStack_cnt-5] = "I&$p2";
			$m=$p2;
			$m++;
			
			push(@semanticStack,$semanticStack[$semanticStack_cnt-5]);
			$semanticStack_cnt++;
			$semanticStack_top++;
			$sempopFlag=0;
		}
		
		#$typeSem = $semanticStack[$semanticStack_cnt-5];
		#now search first in local symbol table 
		#if not present search in global symbol table
		
	}	
	
	if($semanticNum==117)
	{
		#checking the datatypes , so send it to the local sym table and then global sym table
		searchLocalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		if($semLocalEntryFound==0)
		{
				searchGlobalSymbolTable($semanticStack[$semanticStack_cnt-3]);
		}
		#if not found anywhere it is a internediate result
		if($semLocalEntryFound==0 && $semGlobalEntryFound==0)
		{
			$semINTFlag=0;
			$semREALFlag=0;
			if($semanticStack[$semanticStack_cnt]=~m/R/)
			{
				$semREALFlag=1;
			}
			else
			{
				$semINTFlag=1;
			}
			
		}
		
		if($semREALFlag==1)
		{
		updateTuple("R&$m","SUBLOAD","$semanticStack[$semanticStack_cnt-3]","$semanticStack[$semanticStack_cnt-1]");
		$semanticStack[$semanticStack_cnt-3]="R&$m";
		$m++;
		
		push(@semanticStack,$semanticStack[$semanticStack_cnt-3]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$sempopFlag=0;
		}
		else
		{
		updateTuple("I&$m","SUBLOAD","$semanticStack[$semanticStack_cnt-3]","$semanticStack[$semanticStack_cnt-1]");
		$semanticStack[$semanticStack_cnt-3]="I&$m";
		$m++;
		
		push(@semanticStack,$semanticStack[$semanticStack_cnt-3]);
		$semanticStack_cnt++;
		$semanticStack_top++;
		
		$sempopFlag=0;
		}
		
	}
	#for 'lambada' production in betwn 105-124     
	#returned for the constant @si
	if($semanticNum==118)
	{
		push(@semanticStack,pop(@iden_list));
		$semanticStack_cnt++;
		$semanticStack_top++;
	}
	
	if($semanticNum==120)
	{
		$sempopFlag=1;
		#push(@semanticStack,pop(@int_list));
		#$semanticStack_cnt++;
		#$semanticStack_top++;
	}
	if($semanticNum==121)
	{
		
		#push(@semanticStack,pop(@real_list));
		#$semanticStack_cnt++;
		#$semanticStack_top++;
	}	
	
	
	
	
	
	
	
}

sub printSymbolTable
{
	#if($mainFlag[15]==1)
		#{
		    #my $first = $globalSymbolTable[0];
		    
			print SEM "\n\t\t Global Symbol Table is:\n";
			print SEM "\n\t NAME\t:TYPE\t:SHAPE\t:ROWS\t:COLUMNS\t\n ";
			#print SEM "\t\t\t\t test\n";
			my $j2;
			for($j2=0;$j2<=$#globalSymbolTable;$j2++)
			{
		    
			 print SEM "\t\t$globalSymbolTable[$j2]\n";
			
			}
}

sub printLocalSymTable
{
	print SEM "\n\t\t Local Symbol Table is:\n";
	print SEM "\n\t NAME\t:TYPE\t:SHAPE\t:ROWS\t:COLUMNS\t\n ";
			my $j2;
			for($j2=0;$j2<=$#localSymbolTable1;$j2++)
			{
			print SEM "\t\t\t\t$localSymbolTable1[$j2]\n";
			}
}
sub checkError()
  {
  	my $sem_input3;
  	$sem_input3 =$_[0];
    my $semError=0;
    for($j=0;$j<=$#globalST;$j++)
    {
   	 if($sem_input3==$globalST[$j])
   	 {
   		$semError=1;
   		
   	}
   }			
				
				
	if($semError==1)
	{
		print "Variable is already declared \n";
		pop(@globalST);
	}
  }				
sub parser
{
	my $a1;
	my $b1;
	my $c;
	my $y;
	my $z;
	my $i1;
	my $firstHandle=1;

	
	@tmpStack=();
	push(@tmpStack,@stack);
	
	if($stack[$stack_top] eq '%')
	{
		push(@stack,$lexarray[0]);
		push(@semanticStack,$printArray[0]);
		$stack_top++;
		$stack_cnt++;
		$semanticStack_top++;
		$semanticStack_cnt++;
		
	}
	while($lex_cnt<$#lexarray && $lex_cnt<$#printArray)
	{
	# EQUALS/LESS THAN Condition 
	$a1=$stack[$stack_top];
	$b1=$lexarray[$lex_cnt+1];
	$handleNotFound=0;
	
	if($matrix[$a1-1][$b1-1]==1||$matrix[$a1-1][$b1-1]==3)
	{
		push(@stack,$lexarray[$lex_cnt+1]);
		push(@semanticStack,$printArray[$lex_cnt+1]);
		$stack_top++;
		$stack_cnt++;
		$lex_cnt++;
		$semanticStack_top++;
		$semanticStack_cnt++;
	}
	
	# GREATER THAN Condition
	if($matrix[$a1-1][$b1-1]==2)
	{
		$rit1=1;
		#if($mainFlag[12]==1)
		#{	
		#			print SEM "\n\tSemantic Stack Before Reduction is: @semanticStack ";
		#}
		readProd();
		#if($mainFlag[12]==1)
		#{	
		#			print SEM "\n\tSemantic Stack After Reduction is: @semanticStack ";
		#}
		
	}

	#Error Condition
	if($matrix[$a1-1][$b1-1]==0)
	{
		print OP "\n\n\t\t *************** ERROR CONDITION !! *************** \n\n";
		#calculate how much lex tokens u have to skip and go ahead..
		#replace the contents of the stack wd previously stored stack !
		@stack=();
		push(@stack,@tmpStack);
		$stack_top=$#tmpStack;
		$stack_cnt=$#tmpStack;
		$lex_cnt=$totalLexCnt;
	    last;
	}	
   }#end of while 
	$earlierLexCnt = $lex_cnt;
}
sub assemble_code
{
	my ($count)=$_[0];
	
	my $name;
	my $operator;
	my $op1;
	my $op2;
	my @tempTuple;
	my @nextTuple;
	my $checkNextOperator;
	my $parameterCount;
	my @label;
	my $sizeArray;
	
	
	
	@tempTuple = split(',',$tuple[$count]);
	$name=$tempTuple[0];
	$operator=$tempTuple[1];
	$op1=$tempTuple[2];
	$op2=$tempTuple[3];
	$globalop2=$op2;
	@nextTuple = split(',',$tuple[$count+1]);
	$checkNextOperator = $nextTuple[1];
	
	
	#print CODE "\t// EAX: $register[0]\n";
	#print CODE "\t// EBX: $register[1]\n";
	#print CODE "\t// ECX: $register[2]\n";
	#print CODE "\t// EDX: $register[3]\n";
	
	if($operator eq 'INCREMENT')
	{
		print CODE "\t\tinc($name);\n\n"
		
	}
	if($operator eq 'PROGRAMBEGIN')
		{
			print CODE "program $name;\n";
			$programName=$name;
	   		print CODE "#include(\"stdio.hhf\");\n";
	    	print CODE "#include(\"stdlib.hhf\");\n";
            
            print CODE "\t\tstatic\n";
	   		print CODE "\t\ttmp1:int32;\n";
            print CODE "\t\tVR1:int32;\n";
            print CODE "\t\tVR2:int32;\n";
	   		print CODE "\t\tbool:boolean;\n\n";
		}
		
		#case 'MEMORY'
		if($operator eq 'MEMORY')
		{
			 if($op1 eq '4' && $op2 eq '-')
	    	{
				print CODE "\t\t$name:int32;\n\n";
	    	}
	    	elsif($op2 eq '-' && $op1 ne '4')
	    	{
	    		
	    		$sizeArray=($op1/4);
				print CODE "\t\t$name:int32[$sizeArray];\n\n";
			}
	    	else
	    	{
				print CODE "\t\t$name:int32[$op1,$op2];\n\n";
	    	}
			
		}
		
		#case 'ENDDECLARATION'
		if($operator eq 'ENDDECLARATION')
		{
			if($check_if_no_parameter==1)
			{
					print CODE "\t\tbegin $procedure\;\n\n";
			}
		}
		
		#case 'BEGINPROCEDURE'
		if($operator eq 'BEGINPROCEDURE')
		{
			$procedure=$name;
			$procedureString="\t\tprocedure $procedure";
		}
		
		#case 'BEGIN FORMAL PARAMETERS'
		if($operator eq 'BEGIN FORMAL PARAMETERS')
		{
			$procedureString=$procedureString."(";
			#$check_formal_value=1;
		}
		
		#case 'FORMAL.VALUE.PARAMETER.MEMORY'
		if($operator eq 'FORMAL.VALUE.PARAMETER.MEMORY')
		{
			push(@param_list,"$name".":"."dword");
		}
		
		if($operator eq 'FORMAL.REFERENCE.PARAMETER.MEMORY')
		{
			push(@param_list,"var $name".":"."dword");
			$check_ref_value=1;
		}
		
		#case 'ENDFORMALPARAMETERS'
		if($operator eq 'ENDFORMALPARAMETERS')
		{
			$parameters = join(';',@param_list);
			print CODE $procedureString."$parameters\)\;\n";
			if($nextTuple[1] eq 'MEMORY')
			{
				print CODE "\t\tvar\n\n";
			}
			if($nextTuple[1] ne 'MEMORY')
			{
				print CODE "\t\tbegin $procedure\;\n\n";
			}
			@param_list=();
		}
		
		if($operator eq 'INTIALMEMORY')
		{
			print CODE "\t\t$name:int32:=$op2;\n\n";
			
		}
		
		
		
		#case 'IADD'
		if($operator eq 'IADD')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			$reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
				print CODE "\t\tadd($register1,$register2);\n";
				
				if($register2 ne $registerMain[$registerNo1])
                {
                    print CODE "\t\tmov($register2,$registerMain[$registerNo1]);\n\n";
                }
                
							
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
                print CODE "\t\tadd($register2,$register1);\n";
                
                if($register1 ne $registerMain[$registerNo1])
                {
                    print CODE "\t\tmov($register1,$registerMain[$registerNo1]);\n\n";
                    $register[$registerNo1] = '';
                }
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
                print CODE "\t\tadd($register1,$register2);\n";
                
                if($register2 ne $registerMain[$registerNo2])
                {
                    print CODE "\t\tmov($register2,$registerMain[$registerNo2]);\n\n";
                    $register[$registerNo2] = '';
                }
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
				
				$regResult=$registerMain[$regResultNo];
				#$register[$regResultNo]=$name;
				
				print CODE "\t\tadd($register1,$register2);\n";
				
				if($register2 ne $regResult)
				{
					print CODE "\t\tmov($register2,$regResult);\n\n";
					$register[$registerNo2]='';
				}
			}
			
		}
		
		if($operator eq 'STORE') 
		{
			##REFERENCE 
			if($check_ref_value==1)
			{
				$registerNo1 = register_alloc($name);
				$register1 = $registerMain[$registerNo1];
				if($opFound==0)
				{
					print CODE "\t\tmov($name,$register1);\n";
					$register[$registerNo1]=$name;
				}
				print CODE "\t\tmov($op1,(type int32\[$register1\]));\n\n";   
				
			}
			else 
			{
							
				$registerNo1 = register_alloc($op1);
				$register1 = $registerMain[$registerNo1];
				if($opFound==0)
				{
					print CODE "\t\tmov($op1,$register1);\n";
					$register[$registerNo1]=$op1;
				}
				
				for($regCnt=0;$regCnt<$totalReg;$regCnt++)
				{
						if($register[$regCnt] eq $name)
						{
							$register[$regCnt]='';
						}
				}
				
				$register[$registerNo1]=$name;
				print CODE "\t\tmov($register1,$name);\n\n";
				
			}
		}
		
		if($operator eq 'PROCEDURE CALL')
		{
			if($op1 eq 'printf')
			{
				if($nextTuple[2] ne '-')
				{
				print CODE "\t\tstdout.puti32($nextTuple[2]);\n";
				print CODE "\t\tstdout.put(nl);\n"; 
				}
				  
			}
			elsif($op1 eq 'scanf')
			{
				if($nextTuple[2] ne '-')
				{
					print CODE "\t\tstdin.get($nextTuple[2])\;\n\n";
				}
			}
			elsif($nextTuple[1] eq 'NO FORMAL PARAMETERS')
			{
				print CODE "\t\t$name"."(".");\n";
			}
			else ## CALL to a function
			{ 
				$procedureName = "\t\t$name\(";
			}
		}
		
		if($operator eq 'VALUE ACTUAL PARAMETERS')
		{
			push(@param_list,"$op1");
		}
		
		if($operator eq 'REFERENCE ACTUAL PARAMETERS')
		{
			push(@param_list,"$op1");
		}
		
		if($operator eq 'END ACTUAL PARAMETERS LIST')
		{
			$parameters = join(',',@param_list);
			 print CODE $procedureName."$parameters\)\;\n\n";
					
			for($parameterCount=0;$parameterCount<$#param_list;$parameterCount++)
			{
				pop(@param_list);
			}
			
			@param_list=();
			
		}
		if($operator eq 'ENDPROCEDURE')
		{
			print CODE "\t\tend $procedure;\n\n";
			
		}
		
		if($operator eq 'ENDPROGRAM')
		{
			print CODE "\t\tend $programName;\n\n";
			
		}
		if($operator eq 'LABEL')
		{
			if($name eq 'MAIN')
			{
			print CODE "\t\tbegin $programName;\n";
            print CODE "\t\tMAIN:\n\n";
			}
			else
			{
				@label=split(//,$name);
				print CODE "\t\t$label[0]$label[2]$label[3]:\n\n";
			}
			
			##flush out all registers/?
			for($regCnt=0;$regCnt<4;$regCnt++)
			{
				$register[$regCnt]='';
			}
			
			
		}
		
		if($operator eq 'ACTUAL PARAMETERS')
		{
			if($nextTuple[1] eq 'ACTUAL PARAMETERS')
			{
				print CODE "\t\tstdout.puti32($nextTuple[2]);\n";
				print CODE "\t\tstdout.put(nl);\n";   
			}
		}
		
		
		
		
		if($operator eq 'NO FORMAL PARAMETERS')
		{
			if($nextTuple[1] ne 'NO PARAMETERS')
			{
			print CODE $procedureString.";\n";
			
			if($nextTuple[1] eq 'MEMORY')
			{
				print CODE "\t\tvar\n\n";
				$check_if_no_parameter=1;
			}
			if($nextTuple[1] ne 'MEMORY')
			{
				print CODE "\t\tbegin $procedure\;\n\n";
			}
			
			}
			
			
		}
		
		if($operator eq 'NO PARAMETERS')
		{
			#print CODE $procedureName."\)\;\n\n";
			
		}
		
		if($operator eq 'I LESS THAN')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tcmp($register2,$register1);\n";
            print CODE "\t\tsetl(bool);\n\n";
            
            $reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
			
		} #end of ILESSTHAN
		
		
		if($operator eq 'I GREATER THAN')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tcmp($register2,$register1);\n";
            print CODE "\t\tsetg(bool);\n\n";
            
            $reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
			
		} #end of IGREATERTHAN
		
		if($operator eq 'I LESS EQUALS')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tcmp($register2,$register1);\n";
            print CODE "\t\tsetle(bool);\n\n";
            
            $reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
			
		} #end of ILESSEQUALS
		
		if($operator eq 'I GREATER EQUALS')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tcmp($register2,$register1);\n";
            print CODE "\t\tsetge(bool);\n\n";
            
            $reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
			
		} #end of INOTEQUAL
		
		
		if($operator eq 'I NOT EQUAL')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tcmp($register2,$register1);\n";
            print CODE "\t\tsetne(bool);\n\n";
            
            $reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
			
		} #end of INOTEQUAL
		
		if($operator eq 'I EQUAL')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tcmp($register2,$register1);\n";
            print CODE "\t\tsete(bool);\n\n";
            
            $reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
			
		} #end of IEQUAL
		
		
		if($operator eq 'CJUMP')
		{
			$registerNo1=register_alloc($op1);
			$register[$registerNo1]='';
			
			@label=split(//,$name);
			print CODE "\t\tjf (bool) $label[0]$label[2]$label[3];\n\n";
			
		}
		
		
		if($operator eq 'SUB STORE')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tmov($register1,$name\[$register2*4\]);\n\n";
            
            for($regCnt=0;$regCnt<4;$regCnt++)
			{
				if($register[$regCnt] eq $name)
				{
				$register[$regCnt]='';
				}
				
			}
            
            
            $reg1Type = find_reg_type($op1);
            $reg2Type = find_reg_type($op2);
            
           if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo1]=$name;
				$register[$registerNo2]='';
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
			}
		}
		
		
		if($operator eq 'SUBLOAD')
		{
			$registerNo1=register_alloc($op2);
			$register1=$registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register1);\n";
				$register[$registerNo1]=$op2;
			}		
			
			$registerNo2=register_alloc($name);
			$register2=$registerMain[$registerNo2];
			
			
			print CODE "\t\tmov($op1\[$register1*4\],$register2);\n\n";
			
			for($regCnt=0;$regCnt<4;$regCnt++)
			{
				#$register[$regCnt]='';
			}
			
			if(find_reg_type($register[$registerNo1])==3)
			{
				$register[$registerNo1]='';
			}
						
			$register[$registerNo2]=$name;
		}
		
		
		if($operator eq 'ACTUAL SUB PARAMETERS INPUT')
		{
			$registerNo2=register_alloc($op2);
			$register2=$registerMain[$registerNo2];
			
			if($opFound == 0)
            {
                    print CODE "\t\tmov($op2,$register2);\n";
                    $register[$registerNo2]=$op2;
            }
            
            
            print CODE "\n\t\tstdin.geti32();\n";
			print CODE "\t\tmov(ebx,$op1\[$register2*4\]);\n\n";
		}
		
		if($operator eq 'ACTUAL SUB PARAMETERS OUTPUT')
		{
			$registerNo2=register_alloc($op2);
			$register2=$registerMain[$registerNo2];
			
			if($opFound == 0)
            {
                    print CODE "\t\tmov($op2,$register2);\n";
                    $register[$registerNo2]=$op2;
            }
            
            
            
			print CODE "\t\tstdout.puti32($op1\[$register2*4\]);\n\n";
			print CODE "\n\t\tstdout.put(nl);\n";
		}
		
		if($operator eq 'JUMP')
		{
			@label=split(//,$name);
			print CODE "\t\tjmp $label[0]$label[2]$label[3];\n\n";
		}
		
		if($operator eq 'ISUB')
		{
			#1st operand
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			if($opFound==0)
			{
				print CODE "\t\tmov($op1,$register1);\n";
				$register[$registerNo1]=$op1;
			}
			
			#2nd Operand
			$registerNo2 = register_alloc($op2);
			$register2 = $registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tsub($op1,$register2);\n";
				
			for($regCnt=0;$regCnt<4;$regCnt++)
			{
				if($register[$regCnt] eq $name)
				{
				$register[$regCnt]='';
				}
				
			}
			$reg1Type = find_reg_type($op1);
			$reg2Type = find_reg_type($op2);
			
			if($reg1Type==3 && $reg2Type==3)
			{
				$register[$registerNo2]=$name;
				$register[$registerNo1]='';
				print CODE "\t\tmov($register2,$registerMain[$registerNo2]);\n\n";
				
				
			}
			elsif($reg1Type==3)
			{
				$register[$registerNo1]=$name;
				
				print CODE "\t\tmov($register1,$registerMain[$registerNo1]);\n\n";
				
			}
			elsif($reg2Type==3)
			{
				$register[$registerNo2]=$name;
				print CODE "\t\tmov($register2,$registerMain[$registerNo2]);\n\n";
				
			}
			else
			{
				$regResultNo = register_alloc($name);
				$register[$regResultNo]=$name;
				print CODE "\t\tmov($register2,$registerMain[$regResultNo]);\n\n";
				
			}
		}
		
		
		if($operator eq 'IMULT')
		{
			$registerNo1 = register_alloc($op1);
			$register1 = $registerMain[$registerNo1];
			
			if($register1 ne 'eax')
			{
				#$registerNo1 = register_alloc('@');
				#$register1=$registerMain[$registerNo1];
				print CODE "\t\tmov(eax,$register1);\n";
				$register[$registerNo1]=$register[0];
				$register[0]='';
			}
			
			##why to repeat??
			#$registerNo1 = register_alloc($op1);
			#$register1 = $registerMain[$registerNo1];
			
			if(find_reg_type($op1)==3)
			{
				print CODE "\t\tmov($register1,eax);\n";
				$register[0] = $register[$registerNo1];
				$register[$registerNo1]='';
			}
			else
			{
				print CODE "\t\tmov($op1,eax);\n";
				$register[0]=$op1;
			}
			
			##for op2
			$registerNo2 = register_alloc($op2);
			$register2=$registerMain[$registerNo2];
			if($opFound==0)
			{
				print CODE "\t\tmov($op2,$register2);\n";
				$register[$registerNo2]=$op2;
			}
			
			print CODE "\t\tmov(edx,tmp1);\n";
			print CODE "\t\timul($register2);\n\n";
			$register[0]=$name;
			print CODE "\t\tmov(tmp1,edx);\n";
		}
		
	
		
}
sub find_reg_type
{
	my($type)=$_[0];
	my @findTypeOp = split(//,$type);
	my $t1=$findTypeOp[0];
	my $t2=$findTypeOp[1];
	
	if($t2 eq '&')
	{
		return 3; #for INT type
	}
	elsif($t1=~/([a-z][a-z0-9_-]*)/)
	{
		return 2; #for iden
	}
	elsif($t1=~/[0-9]/)
	{
		return 1; #for constant
	}
	
	
}
sub register_alloc
{
	my ($op)=$_[0];
	$opFound=0;
	
	#Find if it is stored in any register
	for($regCnt=0;$regCnt<($totalReg+2);$regCnt++)
	{
		if($op eq $register[$regCnt])
		{
			$opFound=1;
			return $regCnt;
    		  		
		}
	}
	
	#If not stored, store in a register
	for($regCnt=0;$regCnt<$totalReg;$regCnt++)
    {
        if($register[$regCnt] eq '')
        {
        	
            return $regCnt;
            
        }
    }
    
    # for constants 
    for($regCnt=0;$regCnt<$totalReg;$regCnt++)
    {
        if(find_reg_type($register[$regCnt])==1)
        {
        	if($register[$regCnt]!= $globalop2 )
        	{
            return $regCnt;
        	}
            
        }
    }
	
	# for variable
	for($regCnt=0;$regCnt<$totalReg;$regCnt++)
    {
        if(find_reg_type($register[$regCnt])==2)
        {
        	if($register[$regCnt] ne $globalop2)
        	{
            return $regCnt;
        	}
            
        }
    }
	
	
	# for spillage
	for($regCnt=0;$regCnt<$totalReg;$regCnt++)
	{
		if(find_reg_type($register[$regCnt])==3)
		{
			for($spillNum=$totalReg;$spillNum<$totalSpill;$spillNum++)
			{
				if($register[$spillNum] eq '')
				{
					print CODE "\t\tmov($registerMain[$regCnt],$registerMain[$spillNum]);\n";
					$register[$spillNum] = $register[$regCnt];
					$register[$regCnt] = '';
					return $regCnt;
				}
			}
		}
	}
	
	
	
	
	
}

sub pragmatics
{
	my $tupleCount=0;
	my $nextTuple;
	my $maxTupleCount=$#tuple;
	
	my $r1=0;
	
	
	
	
	for($tupleCount=0;$tupleCount<=$maxTupleCount;$tupleCount++)
	{
		print CODE "//Tuple is : ($tuple[$tupleCount])\n\n";
		
		assemble_code($tupleCount);
		
		#print CODE "\t  // EAX: $register[0]\n";
		#print CODE "\t  // EBX: $register[1]\n";
		#print CODE "\t  // ECX: $register[2]\n";
		#print CODE "\t  // EDX: $register[3]\n";
		#print CODE "\t  // VR1: $register[4]\n";
		#print CODE "\t  // VR2: $register[5]\n";
		
	}
	
}
sub main
{
	$totalLexCnt = $#lexarray;
	
	$currentLexCnt = $totalLexCnt - $earlierLexCnt;
	
	if($currentLexCnt > 0)
	{
		$i1=$#sem_list2;
		
		parser();
		
	}
	if($count==$noofLine)
	{
	#parse it for the last line	
	if($lex_cnt==$#lexarray)
	{
		$rit1=1;
		readProd();
		pragmatics();
	}
	    if($mainFlag[16]==1)
	    {
	    printSymbolTable();
	    }
	    
	   
	    
		print "\nProgram Finishes";
		exit;
	}
	else
	{
		my($count)=$_[0];
		$currInput = $inputText[$count];
		@lexString = split ' ',$currInput;
		if($mainFlag[1]==1)
		{
			print OUT "\n $currInput";
			print OP "\n $currInput";
			print SEM "\n $currInput";
			
		}
		lex($currInput);
	}
}

