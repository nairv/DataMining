#include <iostream>
#include <fstream>
#include <string.h>
#include <map>
#include <vector>
#include<sys/time.h>

using namespace std;

//typedef  std::map<string , int >docmap;  // defined in tokenize
std::vector<std::map<string , int> >myvector;
std::vector<string>idvector;
std::vector<string>classvector;
std::map<string , int >stopmap;
std::map<string , int>totalmap;
std::map<string , int>finaltotalmap;
std::multimap<int , int>finalintindexmap;
std::multimap<int , string>finalintstringmap;
std::map<string , int>topicfreqmap;
std::map<string , int >titlemap;
//std::vector<std::map<string, int> >titlevector;

int finaltotalmapsize=0;     // To store the topic strings and their frequencies in the topics tab
string title;               // To store the title

void parseForArticle(char* buffer);
string parseForId(string articleStr);
void parseForTopic(string articleStr , string id);
void parseForTitle(string articleStr , string id);
string parseForBody(string articleStr);
void tokenize(string bodyStr);
void addstopmap();
void createTotalMap(int weight);
void parameterize(int lowerbound , int upperbound);
void stemmer(char *s);
void paramandwritefiles(int lowerbound , int upperbound);

//////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////

#define TRUE 1
#define FALSE 0

/* The main part of the stemming algorithm starts here. b is a buffer
   holding a word to be stemmed. The letters are in b[k0], b[k0+1] ...
   ending at b[k]. In fact k0 = 0 in this demo program. k is readjusted
   downwards as the stemming progresses. Zero termination is not in fact
   used in the algorithm.

   Note that only lower case sequences are stemmed. Forcing to lower case
   should be done before stem(...) is called.
*/

static char * b;       /* buffer for word to be stemmed */
static int k,k0,j;     /* j is a general offset into the string */

/* cons(i) is TRUE <=> b[i] is a consonant. */

static int cons(int i)
{  switch (b[i])
   {  case 'a': case 'e': case 'i': case 'o': case 'u': return FALSE;
      case 'y': return (i==k0) ? TRUE : !cons(i-1);
      default: return TRUE;
   }
}

/* m() measures the number of consonant sequences between k0 and j. if c is
   a consonant sequence and v a vowel sequence, and <..> indicates arbitrary
   presence,

      <c><v>       gives 0
      <c>vc<v>     gives 1
      <c>vcvc<v>   gives 2
      <c>vcvcvc<v> gives 3
      ....
*/

static int m()
{  int n = 0;
   int i = k0;
   while(TRUE)
   {  if (i > j) return n;
      if (! cons(i)) break; i++;
   }
   i++;
   while(TRUE)
   {  while(TRUE)
      {  if (i > j) return n;
            if (cons(i)) break;
            i++;
      }
      i++;
      n++;
      while(TRUE)
      {  if (i > j) return n;
         if (! cons(i)) break;
         i++;
      }
      i++;
   }
}

/* vowelinstem() is TRUE <=> k0,...j contains a vowel */

static int vowelinstem()
{  int i; for (i = k0; i <= j; i++) if (! cons(i)) return TRUE;
   return FALSE;
}

/* doublec(j) is TRUE <=> j,(j-1) contain a double consonant. */

static int doublec(int j)
{  if (j < k0+1) return FALSE;
   if (b[j] != b[j-1]) return FALSE;
   return cons(j);
}

/* cvc(i) is TRUE <=> i-2,i-1,i has the form consonant - vowel - consonant
   and also if the second c is not w,x or y. this is used when trying to
   restore an e at the end of a short word. e.g.

      cav(e), lov(e), hop(e), crim(e), but
      snow, box, tray.

*/

static int cvc(int i)
{  if (i < k0+2 || !cons(i) || cons(i-1) || !cons(i-2)) return FALSE;
   {  int ch = b[i];
      if (ch == 'w' || ch == 'x' || ch == 'y') return FALSE;
   }
   return TRUE;
}

/* ends(s) is TRUE <=> k0,...k ends with the string s. */

static int ends(char * s)
{  int length = s[0];
   if (s[length] != b[k]) return FALSE; /* tiny speed-up */
   if (length > k-k0+1) return FALSE;
   if (memcmp(b+k-length+1,s+1,length) != 0) return FALSE;
   j = k-length;
   return TRUE;
}

/* setto(s) sets (j+1),...k to the characters in the string s, readjusting
   k. */

static void setto(char * s)
{  int length = s[0];
   memmove(b+j+1,s+1,length);
   k = j+length;
}

/* r(s) is used further down. */

static void r(char * s) { if (m() > 0) setto(s); }

/* step1ab() gets rid of plurals and -ed or -ing. e.g.

       caresses  ->  caress
       ponies    ->  poni
       ties      ->  ti
       caress    ->  caress
       cats      ->  cat

       feed      ->  feed
       agreed    ->  agree
       disabled  ->  disable

       matting   ->  mat
       mating    ->  mate
       meeting   ->  meet
       milling   ->  mill
       messing   ->  mess

       meetings  ->  meet

*/

static void step1ab()
{  if (b[k] == 's')
   {  if (ends("\04" "sses")) k -= 2; else
      if (ends("\03" "ies")) setto("\01" "i"); else
      if (b[k-1] != 's') k--;
   }
   if (ends("\03" "eed")) { if (m() > 0) k--; } else
   if ((ends("\02" "ed") || ends("\03" "ing")) && vowelinstem())
   {  k = j;
      if (ends("\02" "at")) setto("\03" "ate"); else
      if (ends("\02" "bl")) setto("\03" "ble"); else
      if (ends("\02" "iz")) setto("\03" "ize"); else
      if (doublec(k))
      {  k--;
         {  int ch = b[k];
            if (ch == 'l' || ch == 's' || ch == 'z') k++;
         }
      }
      else if (m() == 1 && cvc(k)) setto("\01" "e");
   }
}

/* step1c() turns terminal y to i when there is another vowel in the stem. */

static void step1c() { if (ends("\01" "y") && vowelinstem()) b[k] = 'i'; }


/* step2() maps double suffices to single ones. so -ization ( = -ize plus
   -ation) maps to -ize etc. note that the string before the suffix must give
   m() > 0. */

static void step2() { switch (b[k-1])
{
    case 'a': if (ends("\07" "ational")) { r("\03" "ate"); break; }
              if (ends("\06" "tional")) { r("\04" "tion"); break; }
              break;
    case 'c': if (ends("\04" "enci")) { r("\04" "ence"); break; }
              if (ends("\04" "anci")) { r("\04" "ance"); break; }
              break;
    case 'e': if (ends("\04" "izer")) { r("\03" "ize"); break; }
              break;
    case 'l': if (ends("\03" "bli")) { r("\03" "ble"); break; } /*-DEPARTURE-*/

 /* To match the published algorithm, replace this line with
    case 'l': if (ends("\04" "abli")) { r("\04" "able"); break; } */

              if (ends("\04" "alli")) { r("\02" "al"); break; }
              if (ends("\05" "entli")) { r("\03" "ent"); break; }
              if (ends("\03" "eli")) { r("\01" "e"); break; }
              if (ends("\05" "ousli")) { r("\03" "ous"); break; }
              break;
    case 'o': if (ends("\07" "ization")) { r("\03" "ize"); break; }
              if (ends("\05" "ation")) { r("\03" "ate"); break; }
              if (ends("\04" "ator")) { r("\03" "ate"); break; }
              break;
    case 's': if (ends("\05" "alism")) { r("\02" "al"); break; }
              if (ends("\07" "iveness")) { r("\03" "ive"); break; }
              if (ends("\07" "fulness")) { r("\03" "ful"); break; }
              if (ends("\07" "ousness")) { r("\03" "ous"); break; }
              break;
    case 't': if (ends("\05" "aliti")) { r("\02" "al"); break; }
              if (ends("\05" "iviti")) { r("\03" "ive"); break; }
              if (ends("\06" "biliti")) { r("\03" "ble"); break; }
              break;
    case 'g': if (ends("\04" "logi")) { r("\03" "log"); break; } /*-DEPARTURE-*/

 /* To match the published algorithm, delete this line */

} }

/* step3() deals with -ic-, -full, -ness etc. similar strategy to step2. */

static void step3() { switch (b[k])
{
    case 'e': if (ends("\05" "icate")) { r("\02" "ic"); break; }
              if (ends("\05" "ative")) { r("\00" ""); break; }
              if (ends("\05" "alize")) { r("\02" "al"); break; }
              break;
    case 'i': if (ends("\05" "iciti")) { r("\02" "ic"); break; }
              break;
    case 'l': if (ends("\04" "ical")) { r("\02" "ic"); break; }
              if (ends("\03" "ful")) { r("\00" ""); break; }
              break;
    case 's': if (ends("\04" "ness")) { r("\00" ""); break; }
              break;
} }

/* step4() takes off -ant, -ence etc., in context <c>vcvc<v>. */

static void step4()
{  switch (b[k-1])
    {  case 'a': if (ends("\02" "al")) break; return;
       case 'c': if (ends("\04" "ance")) break;
                 if (ends("\04" "ence")) break; return;
       case 'e': if (ends("\02" "er")) break; return;
       case 'i': if (ends("\02" "ic")) break; return;
       case 'l': if (ends("\04" "able")) break;
                 if (ends("\04" "ible")) break; return;
       case 'n': if (ends("\03" "ant")) break;
                 if (ends("\05" "ement")) break;
                 if (ends("\04" "ment")) break;
                 if (ends("\03" "ent")) break; return;
       case 'o': if (ends("\03" "ion") && (b[j] == 's' || b[j] == 't')) break;
                 if (ends("\02" "ou")) break; return;
                 /* takes care of -ous */
       case 's': if (ends("\03" "ism")) break; return;
       case 't': if (ends("\03" "ate")) break;
                 if (ends("\03" "iti")) break; return;
       case 'u': if (ends("\03" "ous")) break; return;
       case 'v': if (ends("\03" "ive")) break; return;
       case 'z': if (ends("\03" "ize")) break; return;
       default: return;
    }
    if (m() > 1) k = j;
}

/* step5() removes a final -e if m() > 1, and changes -ll to -l if
   m() > 1. */

static void step5()
{  j = k;
   if (b[k] == 'e')
   {  int a = m();
      if (a > 1 || a == 1 && !cvc(k-1)) k--;
   }
   if (b[k] == 'l' && doublec(k) && m() > 1) k--;
}

/* In stem(p,i,j), p is a char pointer, and the string to be stemmed is from
   p[i] to p[j] inclusive. Typically i is zero and j is the offset to the last
   character of a string, (p[j+1] == '\0'). The stemmer adjusts the
   characters p[i] ... p[j] and returns the new end-point of the string, k.
   Stemming never increases word length, so i <= k <= j. To turn the stemmer
   into a module, declare 'stem' as extern, and delete the remainder of this
   file.
*/

int stem(char * p, int i, int j)
{  b = p; k = j; k0 = i; /* copy the parameters into statics */
   if (k <= k0+1) return k; /*-DEPARTURE-*/

   /* With this line, strings of length 1 or 2 don't go through the
      stemming process, although no mention is made of this in the
      published algorithm. Remove the line to match the published
      algorithm. */

   step1ab(); step1c(); step2(); step3(); step4(); step5();
   return k;
}
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
//Word stemmer ends here
///////////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////////


//Main function starts here

int main ()
{
    int length;
    char *pch ,*tp;
    string filenum[22] = {"000", "001","002","003","004","005","006","007","008","009","010","011","012","013","014","015","016","017","018","019","020","021"};
    // Opening the file
    double rtclock();
    double clkbegin , clkend , t;
    clkbegin = rtclock();

    addstopmap();

    //while()
    for(int i =0;i <=21;i++){
        ifstream filename;
        string filename11 = "reut2-"+filenum[i]+".sgm";
        const char* filename1 = filename11.c_str();
        filename.open (filename1, ios::binary );

        if(filename.is_open()){
        // get length of file:
        filename.seekg (0, ios::end);
        length = filename.tellg();
        //printf("/n%d",length);

        // Returning the pointer to the beginning of the file
        filename.seekg (0, ios::beg);

        // allocate memory:
        char* buffer = new char [length+1];

        // read data as a block into a variable in memory:
        filename.read (buffer,length);
        filename.close();

        //Parse the buffer variable
        parseForArticle(buffer);

        //Deleting the bugger variable
        delete[] buffer;
        }
    }

    int weight; // weight for the class vectors in the final totalmap

    cout << "\nEnter the weight of the class vectors to be considered in the final frequency vector" <<endl;;
    cin >> weight;
    //weight = 3;

    // Creating the total map of all the words in the dataset
    createTotalMap(weight);

    //cout << "\nPlease enter lower and upper bounds of the frequencies of the words in the final set of feature vectors" << endl;
    int lowerbound , upperbound;
    cout << "Enter the lower bound :";
    cin >> lowerbound;
    //lowerbound = 5;
    cout << endl << "Enter the upper bound :";
    cin >> upperbound;
    //upperbound = 2000;

    cout << "\nThe number of feature vectors in the initial map are : "<< (int)totalmap.size() <<endl;;
    paramandwritefiles(lowerbound ,  upperbound);
    //cout << "\nThe number of feature vectors in the final vector map after the parameter thresholding and calculating weighing factors are :"<< (int)totalmap.size()<<endl;

    cout << "\nThe number of feature vectors in the finaltotalmap after the \nparameter thresholding and calculating weighing factors are :"<< (int)finaltotalmap.size()<<endl;

    clkend = rtclock();

    t = clkend - clkbegin;

    cout <<endl ;
    cout << "\nTime taken for weight " << weight <<" and upperbound and lowerbound as "<< upperbound << " and " << lowerbound <<" respectively is :";
    //cout << endl;
    printf("%.3f\n",t);

    return 0;
}

/*
Function for parameterizing based on freq and writing into files
*/
void paramandwritefiles(int lowerbound , int upperbound)
{
    // Writing of the data structures into the files
    ofstream classfilename , idfilename , myfilename , totalfilename , finalstringinasc ;

    //Writing the original vector of hashmaps into the file which contains all the strings in the body of the text
    myfilename.open("myvector",ios::out | ios::app | ios::binary);
    if(myfilename.is_open())
    {
        for(int i =0 ; i< myvector.size() ; i++)
        {
            //map<string , int >docmap;
            map<string , int>::iterator it;
            pair<map<string , int>::iterator,bool> ret;

            map<string , int > docmap = myvector.at(i);

            myfilename << "< <" << "ID :"<< i+1 << "> <"<< docmap.size() << "> ";
            for (it =  docmap.begin(); it!= docmap.end(); it++)
            {
                myfilename<< "<" << (*it).first << "," << (*it).second << ">";
            }
            myfilename << endl;
        }
    }
    myfilename.close();


    // Parameterizing the thresholds based on the frequencies of the words in the dataset
    parameterize( lowerbound , upperbound);


    // Writing the classvectors in the classvector file
    classfilename.open("classvector",ios::out | ios::app | ios::binary);
    if(classfilename.is_open())
    {
        for(int i =0 ; i< classvector.size() ; i++)
        {
            classfilename<< "<" +classvector.at(i) + ">" << endl;
        }
    }
    classfilename.close();

    // Writing the document ids into id array
    idfilename.open("idvector",ios::out | ios::app | ios::binary);
    if(idfilename.is_open())
    {
        for(int i =0 ; i< idvector.size() ; i++)
        {
            idfilename<< "<" + idvector.at(i) + ">" << endl;
        }
    }
    idfilename.close();

    // Writing the final vector of hashmaps into another file based on the thresholds given
    myfilename.open("myfinalvector",ios::out | ios::app | ios::binary);
    if(myfilename.is_open())
    {
        for(int i =0 ; i< myvector.size() ; i++)
        {
            //map<string , int >docmap;
            map<string , int>::iterator it;
            pair<map<string , int>::iterator,bool> ret;

            map<string , int > docmap = myvector.at(i);

            myfilename << "< <" << "ID :"<< i+1 << "> <"<< docmap.size() << "> ";
            for (it =  docmap.begin(); it!= docmap.end(); it++)
            {
                myfilename<< "<" << (*it).first << "," << (*it).second << ">";
            }
            myfilename << endl;
        }
    }
    myfilename.close();

    // Map of all the words in the body of the text and their frequencies
    totalfilename.open("totalinitmap",ios::out | ios::app | ios::binary);
    if(totalfilename.is_open())
    {
        //map<string , int >docmap;
        map<string , int>::iterator it;
        pair<map<string , int>::iterator,bool> ret;

        //map<string , int > docmap = totalmap.at(i);

        //totalfilename << "< <" << "ID :"<< i<< "> <"<< docmap.size() << "> ";
        for (it =  totalmap.begin(); it!= totalmap.end(); it++)
        {
            totalfilename<< "{ " << (*it).first << " }{ " << (*it).second << " }" << endl;
        }
        totalfilename << endl;

    }
    totalfilename.close();

    //Map of all the strings in ascending order of their frequencies and indexed by the frequencies- multimap
    finalstringinasc.open("finalstringinascmap",ios::out | ios::app | ios::binary);
    if(finalstringinasc.is_open())
    {
        multimap<int , string>::iterator itfs;
        pair<multimap<int , string>::iterator,bool> retfs;

        for(itfs =finalintstringmap.begin(); itfs!= finalintstringmap.end(); itfs++)
        {
            finalstringinasc << "{" << (*itfs).first << " }{ " << (*itfs).second << " }" << endl;
        }
        finalstringinasc<<endl;

    }
    finalstringinasc.close();
}

/*
Parse and get the articles from the files
*/
void parseForArticle(char* buffer)
{
    int i = 1 , found1 = 0 , found2 = 0 , temp;

    string str = buffer, articleStr , bodyStr;
    string topic ,body , id , places , organisation ;

//  First instance of found1
    found1 = str.find("<REUTERS");

    while(found1!= std::string::npos)
    {
        found2 = str.find("</REUTERS>", found1+1);

        articleStr = str.substr(found1 , found2 - found1);

        id = parseForId(articleStr);
        // push the id into the id vector
        idvector.push_back(id);

        parseForTopic(articleStr, id);

        parseForTitle(articleStr , id  );

        bodyStr = parseForBody(articleStr);

        tokenize(bodyStr);

        found1 = str.find("<REUTERS" , found2+1);
    }

}

/*
Parse and get the id from the article string
*/
string parseForId(string articleStr )
{
    string id;
    int found1 = articleStr.find("NEWID=");
    int found2 = articleStr.find("\"",found1+1);
    int found3 = articleStr.find("\"",found2+1);
    id = articleStr.substr(found2+1, found3-found2-1);
    //cout << "ID is " << id << endl;
    return id;
}

/*
Parse for the topic from the article string
*/
void  parseForTopic(string articleStr, string id)
{
    string topic;
    string ftopic = "<" + id + ">";
    int temp, found1 , found2 , found3;
    map<string , int>::iterator it;                 //For topicfrequencies map
    pair<map<string , int>::iterator,bool> ret;     //For topicfrequencies map

    found3 = articleStr.find("</D></TOPICS>");

    if(found3 == std::string::npos)
    {
        //cout << "No topics present" <<endl;
        return ;
    }

    found1 = articleStr.find("<TOPICS><D>");
    found1 = articleStr.find("<D>", found1+1);
    found2 = articleStr.find("</D>", found1+1);


    while(found2 <= found3)
    {
        topic =  articleStr.substr(found1 + 3 , found2 - found1 - 3);

        //Stemming the topic string so that it can be compared with the elements of the body which
        //also goes through the stemming process
        char* topic_cstr = new char[topic.size()+1];
        strcpy(topic_cstr , topic.c_str());
        stemmer(topic_cstr);

        ret = topicfreqmap.insert(pair<string,int>(topic_cstr , 1 ) );
        if(ret.second == false)
        {
            ret.first->second = ret.first->second + 1;
        }
        //cout << "The topic string is " << topic << endl;
        // Pushing the topic into the topicvector
        ftopic = ftopic + "<"+topic_cstr+">";
        //cin >> temp;

        found1 = articleStr.find("<D>", found2+1);
        found2 = articleStr.find("</D>", found1+1);
        if(found1 == std::string::npos || found2 == std::string::npos)
        return ;

    }

    classvector.push_back(ftopic);
}

/*
Parse for the title from the article string
*/
void parseForTitle(string articleStr , string id)
{
    map<string , int>::iterator it;
    pair<map<string , int>::iterator,bool> ret;
    title = "";
    int found1 = articleStr.find("<TITLE>");

    int found2 = articleStr.find("</TITLE>", found1+1);

    if(found1 == std::string::npos || found2 == std::string::npos)
    return ;

    title = articleStr.substr(found1+7 , found2-found1 -7);

    char* title_str = new char[title.size()+1];
    strcpy(title_str, title.c_str());
    title.clear();

    char* pch = strtok (title_str," ,.-<>/\\\"\t\r\n&;@!$\%*()#?^_:~+\'01234567890=[]");

    while (pch != NULL)
    {
        stemmer(pch);
        string str = pch;

        // Checking for the presence of a token in the titlemap datastructure
        // If yes , continue
        // Else , include it in the titlemap datastructure
        if(stopmap.count(str) > 0)
        {
            // Removal of numbers and special characters
            pch = strtok (NULL, " ,.-<>/\\\"\t\r\n&;@!$\%*()#?^_:~+\'0123456789=[]");
            continue;
        }

        title = title + " " + str;

        ret = titlemap.insert(pair<string,int>(str , 1 ) );

        // If the word already exists in the docmap , then increment the value by 1
        if(ret.second == false)
        {
            ret.first->second = ret.first->second + 1;
        }
        // Removal of numbers and special characters
        pch = strtok (NULL, " ,.-<>/\\\"\t\r\n&;@!$\%*()#?^_:~+\'0123456789=[]");
    }
    //title = title_str;
    //cout <<"\ntitle is :\n" << title << endl;

}
/*
Parse and get only the text of the article
*/
string parseForBody(string articleStr)
{
    string bodyStr;
    //cout <<"\ntitle is :\n" << title << endl;
    int found1 = articleStr.find("<BODY>");

    int found2 = articleStr.find("</BODY>", found1+1);

    if(found1 == std::string::npos || found2 == std::string::npos)
    {
        bodyStr.append(title);
        return bodyStr;
    }


    bodyStr = articleStr.substr(found1+6 , found2 - found1 - 6);

    bodyStr.append(title);
    //cout << endl;
    //cout << bodyStr << endl;

    return bodyStr;
}

// Tokenize the strings in the body to get only the alphabetic characters
void tokenize(string bodyStr)
{
    map<string , int >docmap;
    map<string , int>::iterator it;
    pair<map<string , int>::iterator,bool> ret;


    char* cstr = new char[bodyStr.size() + 1];
    strcpy(cstr , bodyStr.c_str());

    // Removal of numbers and special characters
    char* pch = strtok (cstr," ,.-<>/\\\"\t\r\n&;@!$\%*()#?^_:~+\'01234567890=[]");

    while (pch != NULL)
    {
        stemmer(pch);
        string str = pch;

        // Checking for the presence of a token in the stopmap datastructure
        // If yes , continue
        // Else , include it in the docmap datastructure
        if(stopmap.count(str) > 0)
        {
            // Removal of numbers and special characters
            pch = strtok (NULL, " ,.-<>/\\\"\t\r\n&;@!$\%*()#?^_:~+\'0123456789=[]");
            continue;

        }

        ret = docmap.insert(pair<string,int>(str , 1 ) );

        // If the word already exists in the docmap , then increment the value by 1
        if(ret.second == false)
        {
            ret.first->second = ret.first->second + 1;
        }
        // Removal of numbers and special characters
        pch = strtok (NULL, " ,.-<>/\\\"\t\r\n&;@!$\%*()#?^_:~+\'0123456789=[]");
    }

    // Finally push the map into the vector
    myvector.push_back(docmap);

}

/*
Adding the stop words into the stop word map variable
*/
void addstopmap()
{
    map<string , int>::iterator it;
    pair<map<string , int>::iterator,bool> ret;

    ifstream inf("stopwords");

    // If we couldn't open the output file stream for reading
    if (!inf)
    {
        // Print an error and exit
        cerr << "Uh oh, Stopword file could not be opened for reading!" << endl;
    }

    // While there's still stuff left to read
    while (inf)
    {
        //Read stuff from the file into a string and print it
        std::string strInput;
        inf >> strInput;

        ret = stopmap.insert(pair<string,int>(strInput , 1 ) );
        if(ret.second == false)
        {
            ret.first->second = ret.first->second + 1;
        }

        //cout << strInput << endl;
    }

  /*  for(it = stopmap.begin(); it != stopmap.end(); it++)
    {
        cout << (*it).first << endl;

    }
    */
}

// Creating a total map of the words from all the words in the vector of maps
// Weighted frequencies
void createTotalMap(int weight)
{

    map<string , int>::iterator it;                // For totalmap
    pair<map<string , int>::iterator,bool> ret;    // For totalmap

    for(int i =0 ; i< myvector.size() ; i++)
    {
        //map<string , int >docmap;
        map<string , int>::iterator itl;               // For docmap
        pair<map<string , int>::iterator,bool> retl;   // For docmap

        map<string , int > docmap = myvector.at(i);

        for (it =  docmap.begin(); it!= docmap.end(); it++)
        {
            int factor = 0;

            ret = totalmap.insert(pair<string , int>( (*it).first , (*it).second) ) ;
            if(ret.second == false)
            {
                ret.first->second = ret.first->second + (*it).second;
            }
            else
            {
                ret.first->second = (*it).second;
            }

            if(titlemap.count((*it).first) > 0)
            factor = titlemap.find((*it).first)->second;
            //Weight equation applied to frequencies in the totalmap
            ret.first->second = ret.first->second + factor*weight;
        }
    }
}
// Sending parameters to retrieve only the words in the totalmap that fall within the required frequencies and to
// retrieve the relevant feature vectors
void parameterize(int lowerbound , int upperbound)
{
    multimap<int , int>::iterator itfi;
    pair<multimap<int , int>::iterator,bool> retfi;
    multimap<int , string>::iterator itfs;
    pair<multimap<int , string>::iterator,bool> retfs;
    map<string , int>::iterator it2;
    map<string , int>::iterator it3; // For finaltotalmap
    int index;

    // Create the finalindexmap - to store the index references to the  original total map of strings and their frequencies
    // Creates the finalstringmap - to store the string of the thresholded feature vectors based on frequencies , key is the frequency
    // because of the need to sort the map into ascending order of the frequencies

    for (it2 = totalmap.begin(), index=0; it2 != totalmap.end() ; it2++, index++)
    {
        if(((*it2).second < upperbound+1) && ((*it2).second > lowerbound-1)){

            //Inserting the elements of the totalmap into the final index map and the final string map
            finalintindexmap.insert(pair<int , int>((*it2).second , index)) ;
            finalintstringmap.insert(pair<int , string>((*it2).second , (*it2).first ));

            // Create the finaltotalmap which contains only the strings thresholded by the upper and lower bound parameters
            finaltotalmap.insert(pair<string , int>((*it2).first , (*it2).second ));
        }
    }



    //Reducing the dimensionality of the original feature vector
    for(int i =0 ; i< myvector.size() ; i++)
    {
        //map<string , int >docmap;
        map<string , int>::iterator it;
        map<string , int>::iterator itl;
        pair<map<string , int>::iterator,bool> retl;

        map<string , int > docmap = myvector.at(i);

        for (it =  docmap.begin(); it!= docmap.end(); it++)
        {
            // Erasing the map element if that element is not found in the final thresholded map
            if( finaltotalmap.count((*it).first) > 0 )
            {
                finaltotalmapsize++;
                continue;
            }
            else
            {
                docmap.erase(it);
            }
        }
        //Once the document map has been modified , assigning it to its vector position
        myvector.at(i) = docmap;
    }
}

void stemmer(char* s)
{
    int i = 0;
    for(i =0 ;s[i] !='\0' ; i++)
        s[i] = tolower(s[i]);

    s[stem(s,0,i-1)+1] = 0;
}

double rtclock()
{
  struct timezone Tzp;
  struct timeval Tp;
  int stat;
  stat = gettimeofday (&Tp, &Tzp);
  if (stat != 0) printf("Error return from gettimeofday: %d",stat);
  return(Tp.tv_sec + Tp.tv_usec*1.0e-6);
}
