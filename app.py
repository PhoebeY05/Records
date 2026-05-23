from flask import Flask, redirect, session, render_template, request, flash, url_for
from flask_session import Session
from cs50 import SQL
from werkzeug.security import check_password_hash, generate_password_hash
from datetime import date, datetime
import random
import re
import os


app = Flask(__name__)
BOOK_PAGES = {"completed", "unfinished", "tbr"}


# Configure session to use filesystem (instead of signed cookies)
app.config["SESSION_PERMANENT"] = False
app.config["SESSION_TYPE"] = "filesystem"
Session(app)

# Configure CS50 Library to use SQLite database
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "books.db")
db = SQL(f"sqlite:///{DB_PATH}")
today = date.today()


def get_page_from_referrer():
    referrer = request.headers.get("Referer", "")
    for page in BOOK_PAGES:
        if page in referrer:
            return page
    return None

def switch(original, new, book_id):
    original = original.lower()
    new = new.lower()
    latest = db.execute("SELECT * FROM completed WHERE user_id = ? ORDER BY date DESC LIMIT 1", session["user_id"])
    book = db.execute(f"SELECT * FROM {original} WHERE id = ? AND user_id = ?", book_id, session["user_id"])
    db.execute(f"DELETE FROM {original} WHERE id = ? AND user_id = ?", book_id, session["user_id"])
    new_id = db.execute(
        f"INSERT INTO {new} (user_id, book, date, notes, genres, status, series) VALUES (?, ?, ?, ?, ?, ?, ?)",
        session["user_id"],
        book[0]["book"],
        today,
        book[0]["notes"],
        book[0]["genres"],
        book[0]["status"],
        book[0]["series"],
    )
    db.execute("UPDATE combined SET id = ?, page = ? WHERE id = ?", new_id, new, book_id)
    if new == "completed":
        if len(latest) > 0:
            date_format = '%Y-%m-%d'
            prev = datetime.strptime(latest[0]["date"], date_format).date()
            days = (today - prev).days
        else:
            days = 0
        db.execute("UPDATE completed SET days = ? WHERE id = ?", days, new_id)          
    


@app.route("/home", methods = ["GET", "POST"])
def home():
    if request.method == "POST":
        if "timeline" in request.form:
            completed_y = request.form.get("completed")
            unfinished_y = request.form.get("unfinished")
            tbr_y = request.form.get("tbr")
            completed = db.execute("SELECT * FROM completed WHERE strftime('%Y', date) = ? AND user_id = ?", completed_y, session["user_id"])
            unfinished = db.execute("SELECT * FROM unfinished WHERE strftime('%Y', date) = ? AND user_id = ?", unfinished_y, session["user_id"])
            tbr = db.execute("SELECT * FROM tbr WHERE strftime('%Y', date) = ? AND user_id = ?", tbr_y, session["user_id"])
            if completed_y == "" or unfinished_y == "" or tbr_y == "":
                flash("Submission failed! Some fields were not filled in.")
                return redirect("/home")
            else:
                return render_template("home.html", completed=completed, unfinished=unfinished, tbr=tbr)
                
        else:
            duration = request.form.get("duration")
            
            if duration == "day":
                day = db.execute("SELECT * FROM combined WHERE date = ? AND user_id = ?", today, session["user_id"])
                return render_template("home.html", day=day, option="day")
            elif duration == "week":
                week = db.execute("SELECT * FROM combined WHERE strftime('%W', date)  = ? AND user_id = ?", today.strftime("%W"), session["user_id"])
                return render_template("home.html",week=week,option="week")
            elif duration == "month":
                month = db.execute("SELECT * FROM combined WHERE strftime('%m', date) = ? AND user_id = ?", '%02d' % today.month, session["user_id"])
                return render_template("home.html", month=month,option="month")
            else:
                flash("Submission failed! No valid options were selected.")
                return redirect("/home")
       
    else:
        return render_template("home.html")

@app.route("/add", methods = ["GET", "POST"])
def add():
    if request.method == "POST":
        name = request.form.get("book")
        page = request.form.get("destination")
        status = request.form.get("status")
        genres = request.form.get("genres")
        notes = request.form.get("notes")
        series = request.form.get("series")
        latest = db.execute("SELECT * FROM completed WHERE user_id = ? ORDER BY date DESC LIMIT 1", session["user_id"])
        if name != "" and page != "Select page" and status != "":    
            book_id = db.execute(
                f"INSERT INTO {page} (user_id, book, date, notes, genres, status, series) VALUES (?, ?, ?, ?, ?, ?, ?)",
                session["user_id"],
                name,
                today,
                notes,
                genres,
                status,
                series,
            )
            flash('Add Book Success!')
            db.execute("INSERT INTO combined (id, user_id, book, date, page) VALUES (?,?,?,?,?)", book_id, session["user_id"], name, today, page)
            if page == "completed":
                if latest == []:
                    days = 0   
                else:
                    date_format = '%Y-%m-%d'
                    prev = datetime.strptime(latest[0]["date"], date_format).date()
                    days = (today - prev).days
                db.execute("UPDATE completed SET days = ? WHERE id = ?", days, book_id)     
            return redirect("/add")  
        else:
                flash('Add Book Failed! Some fields were not filled in.')
                return redirect("/add") 
       
    else:
        return render_template("add.html")

@app.route("/choose", methods = ["GET", "POST"])
def choose():
    page = get_page_from_referrer()
    if page is None:
        return redirect("/home")
    all = db.execute(f"SELECT * FROM {page}")
    random.shuffle(all)
    if all == []:
        session["selected"] = {"book": "No Books Found", "status":"", "genres": "", "notes":"","series":""}
    else:
        session["selected"] = all[0]
    return redirect(f"/{page}")

@app.route("/delete", methods = ["GET", "POST"])
def delete():
    page = get_page_from_referrer()
    id = request.form.get("book")
    if page is None:
        return redirect("/")
    db.execute(f"DELETE FROM {page} WHERE id = ? AND user_id = ?", id, session["user_id"])
    db.execute("DELETE FROM combined WHERE page = ? AND id = ? AND user_id = ?", page, id, session["user_id"])
    return redirect(f"/{page}")

@app.route("/tbr", methods = ["GET", "POST"])
def tbr():
    if request.method == "POST":
        if "change" in request.form:
            change = request.form.get("change")
            book_id = request.form.get("book")
            temp = re.findall(r'\d+', book_id)
            book_id = list(map(int, temp))[0]
            if change == "tick":
                switch("tbr","completed", book_id)
            elif change == 'cross':
                switch("tbr","unfinished", book_id)
            return redirect("/tbr")
        elif "filter" in request.form:
            if "clear" in request.form:
                return redirect("/tbr")
            else:   
                filter = request.form.get("filter")
                id = session["user_id"]
                if filter in ["genres", "series", "notes"]:
                    books = db.execute(f"SELECT * FROM tbr WHERE {filter} != '' AND user_id = {id}  ORDER BY {filter}")
                else:
                    books = []
                return render_template("tbr.html",books=books,random=session["selected"])
                

    else:
        referrer = request.headers.get("Referer")
        if "tbr" not in referrer:
            session["selected"] =[]
        books = db.execute("SELECT * FROM tbr WHERE user_id = ? ORDER BY date DESC, id DESC", session["user_id"])
        return render_template("tbr.html",books=books,random=session["selected"])
    

@app.route("/completed", methods = ["GET", "POST"])
def completed():
    if request.method=="POST":
        if "book" in request.form:
            id = request.form.get("book")
            times = db.execute("SELECT * FROM completed WHERE id =? AND user_id = ?", id, session["user_id"])[0]["reread"]
            db.execute("UPDATE completed SET reread =? WHERE id =? AND user_id = ?", times+1, id, session["user_id"])
            return redirect("/completed")
        elif "filter" in request.form:
            if "clear" in request.form:
                return redirect("/completed")
            else:   
                filter = request.form.get("filter")
                id = session["user_id"]
                if filter in ["genres", "series", "notes"]:
                    books = db.execute(f"SELECT * FROM completed WHERE {filter} != '' AND user_id = {id}  ORDER BY {filter}")
                else:
                    books = []
                return render_template("completed.html",books=books,random=session["selected"])
    else:
        referrer = request.headers.get("Referer")
        if "completed" not in referrer:
            session["selected"] =[]  
        books = db.execute("SELECT * FROM completed WHERE user_id = ? ORDER BY date DESC, id DESC", session["user_id"]) 
        return render_template("completed.html",books=books,random=session["selected"])
    


@app.route("/unfinished", methods = ["GET", "POST"])
def unfinished():
    if request.method == "POST":
        if "change" in request.form:
            change = request.form.get("change")
            book_id = request.form.get("book")
            temp = re.findall(r'\d+', book_id)
            id = list(map(int, temp))[0]
            if change == "tick":
                switch("unfinished","completed", id)
            elif change == 'cross':
                switch("unfinished","tbr", id)
            return redirect("/unfinished")
        elif "filter" in request.form:
            if "clear" in request.form:
                return redirect("/unfinished")
            else:   
                filter = request.form.get("filter")
                id = session["user_id"]
                if filter in ["genres", "series", "notes"]:
                    books = db.execute(f"SELECT * FROM unfinished WHERE {filter} != '' AND user_id = {id}  ORDER BY {filter}")
                else:
                    books = []
                return render_template("unfinished.html",books=books,random=session["selected"])
        else:
            flash("No valid input detected.")
    else:
        referrer = request.headers.get("Referer")
        if "unfinished" not in referrer:
            session["selected"] =[]
        books = db.execute("SELECT * FROM unfinished WHERE user_id = ? ORDER BY date DESC, id DESC", session["user_id"])
        return render_template("unfinished.html",books=books,random=session["selected"])
    
@app.route("/search", methods = ["GET", "POST"])
def search():
    if request.method == "POST":
        book = request.form.get("search", "").lower()
        exists = db.execute("SELECT * FROM combined WHERE user_id = ? AND book LIKE ?", session["user_id"], '%'+book+'%')
        if not exists:
            flash("No books with similar names found! Try a different keyword? 🤔")
        else:
            results = []
            statuses = []
            for i in exists:
                status = i["page"]
                statuses.append(status)
            statuses = list(set(statuses))
            for s in statuses:
                result = db.execute(f"SELECT * FROM {s} WHERE user_id = ? AND book LIKE ?", session["user_id"], '%'+book+'%')
                for r in result:
                    r["status"] = s
                    results.append(r)
            return render_template("search.html", results=results, search=book)
    return redirect("/home")



@app.route("/", methods=["GET", "POST"])
def login():
    if request.method == "POST":
        username = request.form.get("username")
        password = request.form.get("password")
        user = db.execute("SELECT * FROM users WHERE username = ?", username)
        if len(user) > 0 and check_password_hash(user[0]["hash"], password):
            session["user_id"] = user[0]["id"]
            return redirect("/home")
        else:
            flash("No user found!")
            return redirect("/")
    else:
        return render_template("login.html")
    
@app.route("/logout")
def logout():
    session.clear()
    return redirect("/")

@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "POST":
        username = request.form.get("username")
        password = request.form.get("password")
        confirmation = request.form.get("confirmation")
        exists = db.execute("SELECT * FROM users WHERE username = ?", username)
        if not username or not password or not confirmation:
            flash("Must fill in all fields")
        elif len(exists) > 0:
            flash("Username exists")
        elif password != confirmation:
            flash("Passwords do not match")
        else:
            hash = generate_password_hash(password)
            db.execute("INSERT INTO users (username, hash, date) VALUES (?, ?, ?)", username, hash, today)
            id = db.execute("SELECT id FROM users WHERE username = ?", username)
            session["user_id"] = id[0]["id"]
            return redirect("/home")
        return redirect("/register")
    else:
        return render_template("register.html")
    