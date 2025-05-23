using System;
using System.IO;
using System.Text;
using System.Text.RegularExpressions;
using System.Collections;
using System.Collections.Generic;
using System.Xml;
using System.Linq;
using System.Net;
using DotNetWikiBot;
using System.Threading;
using System.Reflection;
using System.Globalization;
using ErrorProofPageLoadAndSave;

class Version
{
	//class fields
	public DateTime datetime; //point in time when an edit was commited (version was created)
	public string username; //user who made the edit
	public int current_size; //size of the version in bytes
	public int bytecount; //difference in bytes compared to the previous version

	//class constructor
	public Version(DateTime dt, string un, int cs, int bc)
	{
		datetime = dt;
		username = un;
		current_size = cs;
		bytecount = bc;
	}
}

class VersionCollection
{
	//class fields
	public List<Version> versions_list;

	//class constructor
	public VersionCollection() {versions_list = new List<Version>();}

	//class methods
	public void Add(DateTime dt, string un, int cs, int bc) {versions_list.Add( new Version(dt, un, cs, bc) );}
	public Version GetLast() {return versions_list.Last();}

	//method which counts how many bytes were added by a given user during a given period of time
	public int GetByteCountForUser(string username, DateTime start_time, DateTime finish_time)
	{
		int bytecount = 0;
		foreach(Version ver in versions_list)
		{
			if(ver.datetime > finish_time) {continue;} //skip versions that are newer then the end of given period
			if(ver.datetime < start_time) {break;} //if a version older than the start of given period is reached, stop iterating
			if(ver.username==username) {bytecount += ver.bytecount;} //if a version falls into given period, count it in
		}
		return bytecount;
	}

	//method which returns the version, which was the latest at a given point in time
	public Version GetVersionAtDate(DateTime time_point)
	{
		foreach(Version ver in versions_list) {if(ver.datetime <= time_point) {return ver;}}
		return null;
	}

	//method which returns the version, counting from oldest to newest, at which given user achieved given bytecount (sum of differences between versions)
	public Version GetVersionWhereBytecountAchieved(string username, int needed_count)
	{
		int sum = 0;
		for(int i = versions_list.Count-1; i >= 0; i--) //iterate from oldest to newest versions
		{
			if(versions_list[i].datetime<(DateTime)Article.parameters["start_time"] ) {continue;} //skip versions that were made before the contest
			else if(versions_list[i].datetime>(DateTime)Article.parameters["finish_time"] ) {break;} //if a version was reached, which was made after the contest, stop iterating
			else if(versions_list[i].username==username) //if this version was made by given user, count it in
			{
				sum += versions_list[i].bytecount;
				if(sum >= needed_count) {return versions_list[i];}
			}
		}
		return null;
	}
}

class Article
{
	int id = 0, user_n = 0, user_bytecount, wikidata_item, disqualification_reason;
	double country_coef = 0, order_coef = 1;
	string title, username = null;
	bool is_disqualified = false, edited_existing = false, improved_small = false, present_in_recommended = false;
	public DateTime creation_time;
	List<string> countries;

	private static int counter = 0;
	private static int utc_diff;
	private static string red_color = "style=background:#faa | ";
	public static List<int> recommended_wd_list = new List<int>();
	public static Dictionary<string,int> users_ordinals = new Dictionary<string,int>();

	public static string[] disqualification_explanations;

	public static Dictionary<string,string> countries_abbr = new Dictionary<string,string>();
	public static Dictionary<string,double> countries_coefs = new Dictionary<string,double>();
	public static Dictionary<string,object> parameters = new Dictionary<string,object>();

	private static string[] line_parts;
	private static string[] date_parts;

	public static Dictionary<string,int> month_numbers = new Dictionary<string,int>()
	{
		{"січня", 1}, {"лютого", 2}, {"березня", 3}, {"квітня", 4}, {"травня", 5}, {"червня", 6}, 
		{"липня", 7}, {"серпня", 8}, {"вересня", 9}, {"жовтня", 10}, {"листопада", 11}, {"грудня", 12}
	};

	public static void InitializeData()
	{
		foreach (string line in File.ReadAllText("recommended_wd_ids.txt").Replace("\r", "").Split('\n')) {recommended_wd_list.Add(Int32.Parse(line));}
		foreach (string line in File.ReadAllText("countries.txt").Replace("\r", "").Split('\n') )
		{
			line_parts = line.Split('\t');
			countries_abbr.Add(line_parts[0], line_parts[1]);
			countries_coefs.Add(line_parts[0], Double.Parse(line_parts[2], CultureInfo.InvariantCulture) );
		}
		foreach (string line in File.ReadAllText("params.txt").Replace("\r", "").Split('\n') )
		{
			line_parts = line.Replace(": ", ":").Split(':');
			if( line_parts[0].EndsWith("_time") )
			{
				date_parts = line_parts[1].Split('.');
				parameters.Add(line_parts[0], new DateTime(Int32.Parse(date_parts[2]), Int32.Parse(date_parts[1]), Int32.Parse(date_parts[0]), 0, 0, 0));
			}
			else if( line_parts[0].EndsWith("_int") ) {parameters.Add(line_parts[0], Int32.Parse(line_parts[1]) );}
			else {parameters.Add(line_parts[0], line_parts[1]);}
		}
		disqualification_explanations = new string[]
		{
			"Користувач додав до статті менше ніж " + parameters["minimum_article_improv_int"] + " байтів", 
			"Користувач створив статтю меншу за " + parameters["minimum_article_size_int"] + " байтів", 
			"Користувач створив нову статтю не зі списку запропонованих",
			"Користувач створив статтю після завершення конкурсного періоду"
		};
		utc_diff = DateTime.Now.Hour - DateTime.UtcNow.Hour;
		if(utc_diff < 0) {utc_diff += 24;}
	}

	//class constructor
	public Article(Page p_talk)
	{
		string template_text, html_source;
		string list_item, edit_user;
		string[] template_parameters;
		int current_size, bytecount;
		MatchCollection mc; Match m2;
		DateTime dt;
		VersionCollection versions_list;

		title = p_talk.title.Replace("Обговорення:", "");

		//load talk page
		load_again:
		p_talk.Load(); //load talk page wikitext
		p_talk.text = p_talk.text.Replace(" |", "|").Replace("| ", "|").Replace(" =", "=").Replace("= ", "=").Replace(" }", "}"); //truncate all spaces which could get in our way
		mc = Regex.Matches(p_talk.text, "\\{\\{" + parameters["nomination_template_name"] + "\\s*\\|([^\\}]*)\\}\\}", RegexOptions.Singleline); //look for the template call inside the wikitext
		if( mc.Count > 1 )
		{
			Console.WriteLine("WARNING! More than one template found"); Console.ReadKey();
			p_talk = new Page(p_talk.title);
			goto load_again;
		}
		template_text = mc[0].Groups[1].Value.Replace("\n", "").Replace("\r", "");

		//iterate over each parameter of the template call
		template_parameters = template_text.Split('|');
		countries = new List<string>();
		foreach(string param in template_parameters)
		{
			if( param.StartsWith("користувач") ) {username = param.Split('=')[1];}
			else if( param.Contains("створено") ) {}
			else if( param.Contains("доповнено") ) {edited_existing = true;}
			else if( param=="" ) {} //skip empty parameter
			else
			{
				if( !countries_coefs.ContainsKey(param) ) {Console.WriteLine("WARNING! The country '" + param + "' was not found"); Console.ReadKey(); goto load_again;}
				countries.Add(param);
			}
		}
		//if no username was found
		if(username==null)
		{
			Console.WriteLine("WARNING! Username not given"); //give warning
			Console.ReadKey(); //wait for corrections to the talk page to be made
			p_talk = new Page(p_talk.title); //reset the talk page object
			goto load_again; //reload the talk page and process it again
		}

		//load edit history
		using (WebClient client = new WebClient())
		{
			client.Encoding = Encoding.UTF8;
			html_source = client.DownloadString("ht"+"tps://uk.wikipedia.org/w/index.php?title=" + title.Replace(" ", "_").Replace("&", "%26") + "&action=history&limit=500");
			if( html_source.Contains("новіших 5") )
			{
				StringBuilder html_source_sb = new StringBuilder(html_source);
				while( html_source.Contains("rel=\"next\" class=\"mw-nextlink\">старіших 500</a>") )
				{
					html_source = client.DownloadString( "ht"+"tps://uk.wikipedia.org" + Regex.Matches(html_source, "<a href=\"([^\"]+)\" rel=\"next\" class=\"mw-nextlink\">старіших 500</a>")[0].Groups[1].Value );
					html_source_sb.Append( html_source );
				}
				html_source = html_source_sb.ToString();
			}
		}
		
		//get wikidata item
		mc = Regex.Matches(html_source, "<a href=\"ht"+"tps://www.wikidata.org/wiki/Special:EntityPage/Q(\\d+)\" title=\"Посилання на пов’язаний елемент сховища даних \\[g\\]\" accesskey=\"g\"><span>Елемент Вікіданих</span>", RegexOptions.Singleline);
		if(mc.Count>0)
		{
			wikidata_item = Int32.Parse(mc[0].Groups[1].Value);
			present_in_recommended = recommended_wd_list.Contains(wikidata_item);
		}

		//disqualify an article which is not from the list (if contest rules require it)
		if( (string)parameters["allow_recommended_only"]=="true" && !edited_existing && !present_in_recommended) {is_disqualified = true; disqualification_reason = 2;}

		//get all versions
		versions_list = new VersionCollection();
		html_source = Regex.Matches(html_source, "<section id=\"pagehistory\" class=\"mw-pager-body\">.+?</section>", RegexOptions.Singleline)[0].Groups[0].Value;
		foreach(Match m in Regex.Matches(html_source, "<li data-mw-revid=.+?</li>", RegexOptions.Singleline))
		{
			list_item = m.Groups[0].Value.Replace("−", "-");
			if( list_item.Contains("class=\"history-deleted") ) {continue;} //skip deleted versions
			//date
			m2 = Regex.Matches(list_item, "class=\"mw-changeslist-date\" title=\"[^\"]+\">(\\d{2}):(\\d{2}), (\\d{1,2}) ([^\\s]+) (\\d{4})</a>", RegexOptions.Singleline)[0];
			dt = new DateTime(Int32.Parse(m2.Groups[5].Value), month_numbers[m2.Groups[4].Value], Int32.Parse(m2.Groups[3].Value), Int32.Parse(m2.Groups[1].Value), Int32.Parse(m2.Groups[2].Value), 0).AddHours(utc_diff);
			//username
			edit_user = Regex.Matches(list_item, "class=\"(?:mw-redirect |)(?:new mw-userlink|mw-userlink|mw-userlink mw-anonuserlink)\"[^\\>]+><bdi>([^\\<]+)</bdi>", RegexOptions.Singleline)[0].Groups[1].Value;
			//current size
			if( list_item.Contains("data-mw-bytes=\"0\">порожня</span>") ) {current_size = 0;}
			else
			{current_size = Int32.Parse(Regex.Matches(list_item, "<span class=\"history-size mw-diff-bytes\" data-mw-bytes=\"\\d+\">([\\d\\s]+) байт", RegexOptions.Singleline)[0].Groups[1].Value.Replace(""+(char)(160), ""));}
			//bytecount
			bytecount = Int32.Parse(Regex.Matches(list_item, "class=\"mw-plusminus-[a-z]{3,4} mw-diff-bytes\" title=\"[^\"]+\">([^\\<]+)</(?:strong|span)>", RegexOptions.Singleline)[0].Groups[1].Value.Replace(""+(char)(160), ""));
			//add to list
			versions_list.Add(dt, edit_user, current_size, bytecount);
		}
		//check that this user really created this article, if they claim to
		if(!edited_existing && versions_list.GetLast().username!=(Char.ToUpper(username[0])+username.Substring(1)) ) //letter case of the first letter of username does not matter
		{
			Console.WriteLine("WARNING! This user ("+username+") did not create this article, ("+versions_list.GetLast().username+") did"); Console.ReadKey();
			p_talk = new Page(p_talk.title);
			goto load_again;
		}
		//if a new article was created, check that it was created during the needed period
		if(!edited_existing && versions_list.GetLast().datetime<(DateTime)parameters["start_time"] )
		{Console.WriteLine("WARNING! This article was created before contest started - " + versions_list.GetLast().datetime); Console.ReadKey();}
		if(versions_list.GetLast().datetime>(DateTime)parameters["finish_time"])
		{
			is_disqualified = true; disqualification_reason = 3;
			Console.WriteLine("WARNING! This article was created after contest finished - " + versions_list.GetLast().datetime); Console.ReadKey();
		}

		//get article creation time for a new article
		if(!edited_existing) {creation_time = versions_list.GetLast().datetime;}
		//or get the point in time at which user achieved minimal allowed bytecount for an improved article
		else
		{
			Version v = versions_list.GetVersionWhereBytecountAchieved(username, (int)parameters["minimum_article_improv_int"]);
			if(v == null && !is_disqualified) {is_disqualified = true; disqualification_reason = 0;}
			else {creation_time = v.datetime;}
		}

		//get bytecount for this user
		user_bytecount = versions_list.GetByteCountForUser(username, (DateTime)parameters["start_time"], (DateTime)parameters["finish_time"]);
		if(!is_disqualified && !edited_existing && user_bytecount<(int)parameters["minimum_article_size_int"] )
		{is_disqualified = true; disqualification_reason = 1;}

		//get country coeficient
		foreach(string country in countries) {country_coef = Math.Max(country_coef, countries_coefs[country]);}

		//was small article improved
		improved_small = (versions_list.GetLast().datetime < (DateTime)parameters["start_time"]) && (versions_list.GetVersionAtDate((DateTime)parameters["start_time"]).current_size <= (int)parameters["small_article_size_int"]);
	}

	public bool IsDisqualified() {return is_disqualified;}

	public void SetId() {id = ++counter;}
	public void SetUserOrdinal()
	{
		if( !users_ordinals.ContainsKey(username) ) {users_ordinals.Add(username, 0);}
		user_n = ++users_ordinals[username];
		order_coef = Math.Round(Math.Pow(0.99, user_n), 4);
	}

	//method which writes out an article as a row in a wikitable
	public override string ToString()
	{
		List<string> countries_str = new List<string>();
		foreach(string country in countries) { countries_str.Add("{{Прапорець|" + countries_abbr[country] + "}}&nbsp;" + country); }
		if(is_disqualified)
		{
			return "|-\n| [[" + title + "]] || {{U|" + username + "}} || " + (edited_existing?"ні":"так") + 
				" || " + (disqualification_reason==0?"&dash;":creation_time.ToString("dd MMMM yyyy, HH:mm")) + 
				"\n| " + (disqualification_reason<=1?red_color:"") + user_bytecount +
				"\n| " + String.Join("<br/>", countries_str.ToArray()) +
				"\n| " + disqualification_explanations[disqualification_reason];
		}
		else
		{
			return "|-\n| " + id + " || [[" + title + "]] || {{U|" + username + "}} || " + (edited_existing?"ні":"так") + 
				" || " + creation_time.ToString("dd MMMM yyyy, HH:mm") + " || " + user_bytecount + " || " + user_n +
				" || " + String.Join("<br/>", countries_str.ToArray()) + " || " + String.Format("{0:0.0}", country_coef) + " || " + order_coef +
				" || " + (present_in_recommended?"2.0":(improved_small?"1.5":"1.0")) + " || ";
		}
	}
}

class ArticleCollection
{
	private List<Article> articles_list;

	public ArticleCollection() {articles_list = new List<Article>();} //class constructor
	public void Add(Article article) {articles_list.Add(article);} //adds an article to this collection
	public void SortByDate() { articles_list = articles_list.OrderBy(a => a.creation_time).ToList(); } //rearranges all articles in the collections to be in chronological order of creation
	public IEnumerator<Article> GetEnumerator() {return articles_list.GetEnumerator();} //metamethod which allows objects of this class to be iterated using 'foreach'

	//method which writes out an article collection as a set of rows in a wikitable
	public override string ToString()
	{
		StringBuilder res = new StringBuilder();
		foreach(Article a in articles_list) {res.Append("\n").Append( a.ToString() );}
		return res.ToString();
	}
}

class CEE_Bot:Bot
{
	public static Site wiki;
	public static void Main(string[] args)
	{
		Article.InitializeData();

		//log into the site
		ServicePointManager.SecurityProtocol = (SecurityProtocolType)3072;
		wiki = new Site("https://uk.wikipedia.org", (string)Article.parameters["username"], (string)Article.parameters["password"]);

		//load list of pages belonging to certain category
		PageList pages = new PageList(wiki);
		pages.FillFromCategoryTree( (string)Article.parameters["articles_category_name"] );

		//declare list of eligible and disqualified articles
		ArticleCollection articles_eligible = new ArticleCollection();
		ArticleCollection articles_disqualified = new ArticleCollection();

		//distribute articles among lists of eligible articles and disqualified articles
		Article a;
		foreach(Page p in pages)
		{
			if( p.title.Contains("Категорія:") || p.title.Contains("Шаблон:") || p.title.Contains("Вікіпедія:") ) {continue;}
			a = new Article(p);
			if( a.IsDisqualified() ) {articles_disqualified.Add(a);}
			else {articles_eligible.Add(a);}
		}

		//make the list of eligible articles chronological by the time of article creation
		articles_eligible.SortByDate();
		//set identificators and ordinals for each article
		foreach(Article art in articles_eligible)
		{
			art.SetId();
			art.SetUserOrdinal();
		}
		//sort the list of participants by the number of articles they created
		Article.users_ordinals = Article.users_ordinals.OrderByDescending(i => i.Value).ThenBy(i => i.Key).ToDictionary(i => i.Key, i => i.Value);

		//construct wiki page
		StringBuilder final_result = new StringBuilder();
		final_result.Append("== Учасники за кількістю статей ==\n{{div col|colwidth=360px}}\n{| class=\"wikitable sortable\"\n! Учасник || <small>Кіл-ть статей</small>");
		foreach(KeyValuePair<string,int> entry in Article.users_ordinals) {final_result.Append("\n|-\n| {{U|" + entry.Key + "}} || " + entry.Value);}
		final_result.Append("\n|}\n{{div col end}}\n\n== Конкурсні статті ==\n{| class=\"wikitable\"\n");
		final_result.Append("! № || Стаття || Автор || <small>Створена <br/>нова?</small> || <small>Дата створення/<br/>доповнення</small> || Розмір || <small>№ для цього <br/>учасника</small> || Країни || К<sub>к</sub> || K<sub>н</sub> || K<sub>д</sub> || Оцінка журі");
		final_result.Append( articles_eligible.ToString() );
		final_result.Append("\n|}\n\n== Дискваліфіковані статті ==\n{| class=\"wikitable\"\n");
		final_result.Append("! Стаття || Автор || <small>Створена <br/>нова?</small> || <small>Дата створення/<br/>доповнення</small> || Розмір || Країни || Причина дискваліфікації");
		final_result.Append( articles_disqualified.ToString() );
		final_result.Append("\n|}\n");

		//save to file
		File.WriteAllText("result.txt", final_result.ToString() );

		Console.WriteLine("\nDONE!");
	}
}
